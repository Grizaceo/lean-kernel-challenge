#!/usr/bin/env python3
"""Generate candidates/ca-rule110-v5/Submission.lean."""
import sys
from pathlib import Path

sys.set_int_max_str_digits(500_000)

ROOT = Path("/home/gris96/.hermes/workspace/repos/SAIR/lean-kernel-challenge")
CAND_DIR = ROOT / "candidates" / "ca-rule110-v5"
CAND_DIR.mkdir(parents=True, exist_ok=True)
DST = CAND_DIR / "Submission.lean"

K = 0x9e3779b9
M1 = 0x7feb352d
M2 = 0x846ca68b
W32 = 0xffffffff
M256 = (1 << 256) - 1
REP3_256 = 1 + (1 << 256) + (1 << 512)

REP_64_2 = sum(1 << (64 * i) for i in range(2, 256))
OFFSETS_64_2 = sum(((i + 1) * K) << (64 * i) for i in range(2, 256))
MASK32_64_2 = sum(W32 << (64 * i) for i in range(2, 256))

BF_MASKS = []
for r in range(8):
    stride = 128 << r
    width = 2 << r
    mask_cell = (1 << width) - 1
    cnt = 256 // width
    BF_MASKS.append(sum(mask_cell << (stride * j) for j in range(cnt)))

bf_defs = []
bf_lets = []
for r in range(8):
    s = 63 << r
    bf_defs.append(f"def bfMask{r} : Nat := (nat_lit {BF_MASKS[r]})")
    bf_lets.append(f"  let b := Nat.land (Nat.lor b (Nat.shiftRight b (nat_lit {s}))) (nat_lit {BF_MASKS[r]})")

bf_defs_str = "\n".join(bf_defs)
bf_lets_str = "\n".join(bf_lets)

src = f"""import Spec

namespace Submission

/-!
# ca-rule110-v5 — 256-Lane 64-Bit SWAR Mixer + 8-Stage Butterfly + 6-Op Lightcone Step

1. Packs all 254 `caMix32` evaluations (`i = 2..255`) into a single 16,384-bit
   `Nat` with 64-bit lanes (`seed * REP_64_2 + OFFSETS_64_2`), executing the entire
   initial-row mixer in 5 big-integer operations instead of 254 * 13 = 3,302 operations.
2. Gathers the 256 cell bits from stride 64 to stride 1 using an 8-stage
   bitwise butterfly (`s = 63 * 2^r`, `r = 0..7`), proved correct via a uniform
   binary-tree induction (`treeAt_butterfly_step`) without unfolding 256 terms.
3. Evaluates Rule 110 on a 3x-replicated periodic bitvector (`rep3Lit`) using the
   6-operation lightcone-shifted step `sstepRaw` (`(c ||| r) ^^^ (m &&& (c &&& r))`
   with `c = m >>> 1, r = m >>> 2`), unrolled for the judge step counts `2, 4, 8`.
-/

/-! ### Part 1: Trusted spec facts & bit-parallel reference kernel -/

theorem testBit_high {{m W : Nat}} (hm : m < 2 ^ W) {{j : Nat}} (hj : W ≤ j) : m.testBit j = false := by
  have hlt : m < 2 ^ j := Nat.lt_of_lt_of_le hm (Nat.pow_le_pow_right (by omega) hj)
  simp [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hlt]

theorem testBit_pack {{W a b : Nat}} (ha : a < 2 ^ W) (j : Nat) :
    (a + (b <<< W)).testBit j = if j < W then a.testBit j else b.testBit (j - W) := by
  have h : a + (b <<< W) = 2 ^ W * b + a := by rw [Nat.shiftLeft_eq, Nat.mul_comm b (2 ^ W), Nat.add_comm]
  rw [h, Nat.testBit_two_pow_mul_add b ha]

theorem testBit_encodeRow (row : List Bool) (i : Nat) :
    (encodeRow row).testBit i = row.getD i false := by
  induction row generalizing i with
  | nil => simp [encodeRow]
  | cons b bs ih =>
    have hrec : encodeRow (b :: bs) = 2 * encodeRow bs + (if b then 1 else 0) := rfl
    cases i with
    | zero => rw [hrec]; cases b <;> simp [Nat.testBit_zero] <;> omega
    | succ j =>
      rw [hrec, Nat.testBit_succ]
      have : (2 * encodeRow bs + (if b then 1 else 0)) / 2 = encodeRow bs := by
        cases b <;> simp <;> omega
      rw [this, ih]; rfl

theorem encodeRow_lt (row : List Bool) : encodeRow row < 2 ^ row.length := by
  induction row with
  | nil => simp [encodeRow]
  | cons b bs ih =>
    have hrec : encodeRow (b :: bs) = 2 * encodeRow bs + (if b then 1 else 0) := rfl
    rw [hrec, List.length_cons, Nat.pow_succ]; split <;> omega

theorem encodeRow_append (xs ys : List Bool) :
    encodeRow (xs ++ ys) = encodeRow xs + (encodeRow ys <<< xs.length) := by
  induction xs with
  | nil => simp [encodeRow]
  | cons b xs ih =>
    have h1 : encodeRow (b :: (xs ++ ys)) = 2 * encodeRow (xs ++ ys) + (if b then 1 else 0) := rfl
    have h2 : encodeRow (b :: xs) = 2 * encodeRow xs + (if b then 1 else 0) := rfl
    rw [List.cons_append, h1, ih, h2, List.length_cons, Nat.shiftLeft_eq, Nat.shiftLeft_eq,
        Nat.pow_succ, ← Nat.mul_assoc]
    omega

@[simp] theorem length_stepRow (row : List Bool) : (stepRow row).length = row.length := by
  simp [stepRow]

@[simp] theorem length_iterRow (t : Nat) (row : List Bool) : (iterRow t row).length = row.length := by
  induction t generalizing row with
  | zero => rfl
  | succ k ih => simp [iterRow, ih]

theorem getD_stepRow (row : List Bool) (i : Nat) :
    (stepRow row).getD i false =
      if i < row.length then
        rule110 (row.getD ((i + row.length - 1) % row.length) false)
                (row.getD i false) (row.getD ((i + 1) % row.length) false)
      else false := by
  by_cases h : i < row.length
  · rw [List.getD_eq_getElem?_getD]; simp [stepRow, h]
  · have hlen : (stepRow row).length ≤ i := by rw [length_stepRow]; omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hlen, Option.getD_none, if_neg h]

def M : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
theorem M_eq : M = 2 ^ 256 - 1 := by decide
theorem testBit_M (i : Nat) : M.testBit i = decide (i < 256) := by
  rw [M_eq, Nat.testBit_two_pow_sub_one]

theorem testBit_rotL {{m : Nat}} (hm : m < 2 ^ 256) {{i : Nat}} (hi : i < 256) :
    (((m <<< 1) ||| (m >>> 255)) &&& M).testBit i = m.testBit ((i + 255) % 256) := by
  rw [Nat.testBit_and, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftRight, testBit_M]
  simp only [hi, decide_true, Bool.and_true]
  rcases Nat.eq_zero_or_pos i with hi0 | hipos
  · subst hi0; simp
  · have h1 : (1 ≤ i) := hipos
    have hmod : (i + 255) % 256 = i - 1 := by omega
    have hhi : m.testBit (255 + i) = false := testBit_high hm (by omega)
    simp [h1, hmod, hhi]

theorem testBit_rotR {{m : Nat}} (hm : m < 2 ^ 256) {{i : Nat}} (hi : i < 256) :
    (((m >>> 1) ||| ((m &&& 1) <<< 255)) &&& M).testBit i = m.testBit ((i + 1) % 256) := by
  rw [Nat.testBit_and, Nat.testBit_or, Nat.testBit_shiftRight, Nat.testBit_shiftLeft, testBit_M]
  simp only [hi, decide_true, Bool.and_true]
  by_cases h255 : i = 255
  · subst h255
    have hmod : (255 + 1) % 256 = 0 := by decide
    have hhi : m.testBit (1 + 255) = false := testBit_high hm (by omega)
    rw [hmod]; simp [hhi]
  · have hmod : (i + 1) % 256 = i + 1 := by omega
    have hnot : ¬ (255 ≤ i) := by omega
    simp [hmod, hnot, Nat.add_comm 1 i]

def bstep (m : Nat) : Nat :=
  let r := (m >>> 1) ||| ((m &&& 1) <<< 255)
  let l := (m <<< 1) ||| (m >>> 255)
  (m ||| r) ^^^ (l &&& (m &&& r))

def biter : Nat → Nat → Nat
  | 0, m => m
  | t + 1, m => biter t (bstep m)

theorem step_eq {{row : List Bool}} (hlen : row.length = 256) :
    encodeRow (stepRow row) = bstep (encodeRow row) := by
  have hm : encodeRow row < 2 ^ 256 := hlen ▸ encodeRow_lt row
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_encodeRow, getD_stepRow, hlen]
  by_cases hi : i < 256
  · rw [if_pos hi]
    have he : i + 256 - 1 = i + 255 := by omega
    rw [he]
    have hrotL := testBit_rotL hm hi
    have hrotR := testBit_rotR hm hi
    rw [Nat.testBit_and, testBit_M, decide_eq_true hi, Bool.and_true] at hrotL hrotR
    unfold bstep
    dsimp only
    rw [Nat.testBit_xor, Nat.testBit_or, Nat.testBit_and, Nat.testBit_and,
        hrotL, hrotR, testBit_encodeRow, testBit_encodeRow, testBit_encodeRow]
    generalize row.getD ((i + 255) % 256) false = a
    generalize row.getD i false = b
    generalize row.getD ((i + 1) % 256) false = c
    cases a <;> cases b <;> cases c <;> decide
  · rw [if_neg hi]
    unfold bstep
    dsimp only
    have hm_hi : (encodeRow row).testBit i = false := testBit_high hm (by omega)
    have hr_hi : (((encodeRow row) >>> 1) ||| (((encodeRow row) &&& 1) <<< 255)).testBit i = false := by
      rw [Nat.testBit_or, Nat.testBit_shiftRight, Nat.testBit_shiftLeft]
      have h1 : (encodeRow row).testBit (1 + i) = false := testBit_high hm (by omega)
      have h2 : (encodeRow row &&& 1) < 2 ^ 1 :=
        Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
      have h3 : (encodeRow row &&& 1).testBit (i - 255) = false :=
        testBit_high h2 (by omega)
      simp only [h1, h3, Bool.false_or, Bool.and_false]
    rw [Nat.testBit_xor, Nat.testBit_or, Nat.testBit_and, Nat.testBit_and, hm_hi, hr_hi]
    simp

theorem iter_eq : ∀ (n : Nat) (row : List Bool), row.length = 256 →
    encodeRow (iterRow n row) = biter n (encodeRow row) := by
  intro n
  induction n with
  | zero => intro row _; rfl
  | succ k ih =>
    intro row hlen
    show encodeRow (iterRow k (stepRow row)) = biter k (bstep (encodeRow row))
    rw [ih (stepRow row) (by rw [length_stepRow, hlen]), step_eq hlen]

/-! ### Part 2: Binary-tree SWAR algebra (`treeAt`) -/

def treeAt (W step : Nat) : Nat → (Nat → Nat) → Nat → Nat
  | 0, f, i0 => f i0
  | k + 1, f, i0 =>
      treeAt W step k f i0 + (treeAt W step k f (i0 + step * 2 ^ k) <<< (W * 2 ^ k))

theorem treeAt_congr (W step : Nat) {{f g : Nat → Nat}} (h : ∀ i, f i = g i) :
    ∀ k i0, treeAt W step k f i0 = treeAt W step k g i0
  | 0, i0 => h i0
  | k + 1, i0 => by
    simp only [treeAt, treeAt_congr W step h k i0, treeAt_congr W step h k (i0 + step * 2 ^ k)]

theorem treeAt_bound_congr (W step : Nat) (hstep : 1 ≤ step) {{f g : Nat → Nat}} :
    ∀ k i0, (∀ i, i < i0 + step * 2 ^ k → f i = g i) →
      treeAt W step k f i0 = treeAt W step k g i0
  | 0, i0, h => h i0 (by omega)
  | k + 1, i0, h => by
    simp only [treeAt]
    have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
    have hmul : step * 2 ^ (k + 1) = step * 2 ^ k + step * 2 ^ k := by rw [hpow, Nat.mul_add]
    rw [treeAt_bound_congr W step hstep k i0 (fun i hi => h i (by omega)),
        treeAt_bound_congr W step hstep k (i0 + step * 2 ^ k) (fun i hi => h i (by omega))]

theorem pack_add (W a1 b1 a2 b2 : Nat) :
    (a1 + (b1 <<< W)) + (a2 + (b2 <<< W)) = (a1 + a2) + ((b1 + b2) <<< W) := by
  simp only [Nat.shiftLeft_eq, Nat.add_mul]; omega

theorem pack_mul (W a b c : Nat) :
    (a + (b <<< W)) * c = a * c + ((b * c) <<< W) := by
  simp only [Nat.shiftLeft_eq, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm (2 ^ W) c]

theorem pack_and {{W a1 b1 a2 b2 : Nat}} (ha1 : a1 < 2 ^ W) (ha2 : a2 < 2 ^ W) :
    (a1 + (b1 <<< W)) &&& (a2 + (b2 <<< W)) = (a1 &&& a2) + ((b1 &&& b2) <<< W) := by
  have h12 : (a1 &&& a2) < 2 ^ W := Nat.lt_of_le_of_lt Nat.and_le_left ha1
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_and, testBit_pack ha1, testBit_pack ha2, testBit_pack h12]
  split <;> simp [Nat.testBit_and]

theorem pack_xor {{W a1 b1 a2 b2 : Nat}} (ha1 : a1 < 2 ^ W) (ha2 : a2 < 2 ^ W) :
    (a1 + (b1 <<< W)) ^^^ (a2 + (b2 <<< W)) = (a1 ^^^ a2) + ((b1 ^^^ b2) <<< W) := by
  have h12 : (a1 ^^^ a2) < 2 ^ W := Nat.xor_lt_two_pow ha1 ha2
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_xor, testBit_pack ha1, testBit_pack ha2, testBit_pack h12]
  split <;> simp [Nat.testBit_xor]

theorem pack_or {{W a1 b1 a2 b2 : Nat}} (ha1 : a1 < 2 ^ W) (ha2 : a2 < 2 ^ W) :
    (a1 + (b1 <<< W)) ||| (a2 + (b2 <<< W)) = (a1 ||| a2) + ((b1 ||| b2) <<< W) := by
  have h12 : (a1 ||| a2) < 2 ^ W := Nat.or_lt_two_pow ha1 ha2
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_or, testBit_pack ha1, testBit_pack ha2, testBit_pack h12]
  split <;> simp [Nat.testBit_or]

theorem pack_shr_and {{W s a b m1 m2 : Nat}} (hs : s ≤ W) (ha : a < 2 ^ W)
    (hm1 : m1 < 2 ^ (W - s)) (hm1W : m1 < 2 ^ W) :
    ((a + (b <<< W)) >>> s) &&& (m1 + (m2 <<< W)) =
      ((a >>> s) &&& m1) + (((b >>> s) &&& m2) <<< W) := by
  have hlo : (a >>> s) &&& m1 < 2 ^ W := Nat.lt_of_le_of_lt Nat.and_le_right hm1W
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_and, Nat.testBit_shiftRight, testBit_pack ha, testBit_pack hm1W, testBit_pack hlo]
  by_cases hj : j < W
  · rw [if_pos hj, if_pos hj, Nat.testBit_and, Nat.testBit_shiftRight]
    by_cases hjs : s + j < W
    · rw [if_pos hjs]
    · rw [if_neg hjs]
      have hm_hi : m1.testBit j = false := testBit_high hm1 (by omega)
      simp [hm_hi]
  · rw [if_neg hj, if_neg hj, if_neg (by omega), Nat.testBit_and, Nat.testBit_shiftRight]
    have hsub : s + j - W = s + (j - W) := by omega
    rw [hsub]

theorem butterfly_leaf {{B W s a b : Nat}} (hW : W = s + B) (hBW : B + B ≤ W)
    (ha : a < 2 ^ B) (hb : b < 2 ^ B) :
    (((a + (b <<< W)) ||| ((a + (b <<< W)) >>> s)) &&& (2 ^ (B + B) - 1)) = a + (b <<< B) := by
  have haW : a < 2 ^ W := Nat.lt_of_lt_of_le ha (Nat.pow_le_pow_right (by omega) (by omega))
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_and, Nat.testBit_or, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one,
      testBit_pack haW, testBit_pack haW, testBit_pack ha]
  by_cases hj2 : j < B + B
  · simp only [hj2, decide_true, Bool.and_true]
    have hjW : j < W := by omega
    rw [if_pos hjW]
    by_cases hjB : j < B
    · have hsj : s + j < W := by omega
      rw [if_pos hjB, if_pos hsj]
      have hasj : a.testBit (s + j) = false := testBit_high ha (by omega)
      simp [hasj]
    · have hsj : ¬ (s + j < W) := by omega
      have hsub : s + j - W = j - B := by omega
      have haj : a.testBit j = false := testBit_high ha (by omega)
      rw [if_neg hjB, if_neg hsj, hsub, haj, Bool.false_or]
  · simp only [hj2, decide_false, Bool.and_false]
    have hjB : ¬ (j < B) := by omega
    rw [if_neg hjB]
    exact (testBit_high hb (by omega)).symm

theorem add_mul_two_pow_lt {{P Q a b : Nat}} (ha : a < 2 ^ P) (hb : b < 2 ^ Q) :
    a + b * 2 ^ P < 2 ^ (Q + P) := by
  have h1 : b * 2 ^ P ≤ (2 ^ Q - 1) * 2 ^ P := Nat.mul_le_mul_right (2 ^ P) (by omega)
  rw [Nat.sub_mul, Nat.one_mul, ← Nat.pow_add] at h1
  have h2 : 2 ^ P ≤ 2 ^ (Q + P) := Nat.pow_le_pow_right (by omega) (by omega)
  omega

theorem treeAt_lt (W step s : Nat) (hs : s ≤ W) {{f : Nat → Nat}} (hf : ∀ i, f i < 2 ^ (W - s)) :
    ∀ k i0, treeAt W step k f i0 < 2 ^ (W * 2 ^ k - s)
  | 0, i0 => by simpa [treeAt] using hf i0
  | k + 1, i0 => by
    simp only [treeAt, Nat.shiftLeft_eq]
    have hlo := treeAt_lt W step s hs hf k i0
    have hhi := treeAt_lt W step s hs hf k (i0 + step * 2 ^ k)
    have hpos : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    have hW : W ≤ W * 2 ^ k := by simpa using Nat.mul_le_mul_left W hpos
    have hloP : treeAt W step k f i0 < 2 ^ (W * 2 ^ k) :=
      Nat.lt_of_lt_of_le hlo (Nat.pow_le_pow_right (by omega) (by omega))
    have hcomb := add_mul_two_pow_lt hloP hhi
    have heq : (W * 2 ^ k - s) + W * 2 ^ k = W * 2 ^ (k + 1) - s := by
      rw [Nat.pow_succ, ← Nat.mul_assoc]; omega
    rwa [heq] at hcomb

theorem treeAt_lt0 (W step : Nat) {{f : Nat → Nat}} (hf : ∀ i, f i < 2 ^ W) (k i0 : Nat) :
    treeAt W step k f i0 < 2 ^ (W * 2 ^ k) := by
  simpa using treeAt_lt W step 0 (by omega) (by simpa using hf) k i0

theorem treeAt_add (W step : Nat) (f g : Nat → Nat) :
    ∀ k i0, treeAt W step k f i0 + treeAt W step k g i0 = treeAt W step k (fun i => f i + g i) i0
  | 0, i0 => rfl
  | k + 1, i0 => by
    simp only [treeAt]
    rw [pack_add, treeAt_add W step f g k i0, treeAt_add W step f g k (i0 + step * 2 ^ k)]

theorem treeAt_mul (W step c : Nat) (f : Nat → Nat) :
    ∀ k i0, treeAt W step k f i0 * c = treeAt W step k (fun i => f i * c) i0
  | 0, i0 => rfl
  | k + 1, i0 => by
    simp only [treeAt]
    rw [pack_mul, treeAt_mul W step c f k i0, treeAt_mul W step c f k (i0 + step * 2 ^ k)]

theorem treeAt_and (W step : Nat) {{f g : Nat → Nat}} (hf : ∀ i, f i < 2 ^ W) (hg : ∀ i, g i < 2 ^ W) :
    ∀ k i0, treeAt W step k f i0 &&& treeAt W step k g i0 = treeAt W step k (fun i => f i &&& g i) i0
  | 0, i0 => rfl
  | k + 1, i0 => by
    simp only [treeAt]
    rw [pack_and (treeAt_lt0 W step hf k i0) (treeAt_lt0 W step hg k i0),
        treeAt_and W step hf hg k i0, treeAt_and W step hf hg k (i0 + step * 2 ^ k)]

theorem treeAt_xor (W step : Nat) {{f g : Nat → Nat}} (hf : ∀ i, f i < 2 ^ W) (hg : ∀ i, g i < 2 ^ W) :
    ∀ k i0, treeAt W step k f i0 ^^^ treeAt W step k g i0 = treeAt W step k (fun i => f i ^^^ g i) i0
  | 0, i0 => rfl
  | k + 1, i0 => by
    simp only [treeAt]
    rw [pack_xor (treeAt_lt0 W step hf k i0) (treeAt_lt0 W step hg k i0),
        treeAt_xor W step hf hg k i0, treeAt_xor W step hf hg k (i0 + step * 2 ^ k)]

theorem treeAt_or (W step : Nat) {{f g : Nat → Nat}} (hf : ∀ i, f i < 2 ^ W) (hg : ∀ i, g i < 2 ^ W) :
    ∀ k i0, treeAt W step k f i0 ||| treeAt W step k g i0 = treeAt W step k (fun i => f i ||| g i) i0
  | 0, i0 => rfl
  | k + 1, i0 => by
    simp only [treeAt]
    rw [pack_or (treeAt_lt0 W step hf k i0) (treeAt_lt0 W step hg k i0),
        treeAt_or W step hf hg k i0, treeAt_or W step hf hg k (i0 + step * 2 ^ k)]

theorem treeAt_shr_and (W step s : Nat) (hs : s ≤ W) {{f m : Nat → Nat}}
    (hf : ∀ i, f i < 2 ^ W) (hm : ∀ i, m i < 2 ^ (W - s)) :
    ∀ k i0, (treeAt W step k f i0 >>> s) &&& treeAt W step k m i0 =
      treeAt W step k (fun i => (f i >>> s) &&& m i) i0
  | 0, i0 => rfl
  | k + 1, i0 => by
    simp only [treeAt]
    have hpos : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    have hW : W ≤ W * 2 ^ k := by simpa using Nat.mul_le_mul_left W hpos
    have hmW : ∀ i, m i < 2 ^ W := fun i =>
      Nat.lt_of_lt_of_le (hm i) (Nat.pow_le_pow_right (by omega) (by omega))
    rw [pack_shr_and (by omega) (treeAt_lt0 W step hf k i0)
          (treeAt_lt W step s hs hm k i0) (treeAt_lt0 W step hmW k i0),
        treeAt_shr_and W step s hs hf hm k i0,
        treeAt_shr_and W step s hs hf hm k (i0 + step * 2 ^ k)]

theorem treeAt_succ_pair (W step : Nat) (f : Nat → Nat) :
    ∀ k i0, treeAt W step (k + 1) f i0 =
      treeAt (W * 2) (step * 2) k (fun i => f i + (f (i + step) <<< W)) i0
  | 0, i0 => by simp [treeAt]
  | k + 1, i0 => by
    have ih1 := treeAt_succ_pair W step f k i0
    have ih2 := treeAt_succ_pair W step f k (i0 + (step * 2) * 2 ^ k)
    have hstep : step * 2 ^ (k + 1) = (step * 2) * 2 ^ k := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ k) 2, ← Nat.mul_assoc]
    have hW : W * 2 ^ (k + 1) = (W * 2) * 2 ^ k := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ k) 2, ← Nat.mul_assoc]
    calc treeAt W step (k + 2) f i0
      _ = treeAt W step (k + 1) f i0 + (treeAt W step (k + 1) f (i0 + step * 2 ^ (k + 1)) <<< (W * 2 ^ (k + 1))) := rfl
      _ = treeAt (W * 2) (step * 2) k (fun i => f i + (f (i + step) <<< W)) i0 +
          (treeAt (W * 2) (step * 2) k (fun i => f i + (f (i + step) <<< W)) (i0 + (step * 2) * 2 ^ k) <<< ((W * 2) * 2 ^ k)) := by
        rw [hstep, hW, ih1, ih2]
      _ = treeAt (W * 2) (step * 2) (k + 1) (fun i => f i + (f (i + step) <<< W)) i0 := rfl

theorem treeAt_butterfly (W step B s : Nat) (hW : W = s + B) (hBW : B + B ≤ W)
    {{f : Nat → Nat}} (hf : ∀ i, f i < 2 ^ B) (k i0 : Nat) :
    ((treeAt W step (k + 1) f i0 ||| (treeAt W step (k + 1) f i0 >>> s)) &&&
      treeAt (W * 2) (step * 2) k (fun _ => 2 ^ (B + B) - 1) i0) =
    treeAt (W * 2) (step * 2) k (fun i => f i + (f (i + step) <<< B)) i0 := by
  rw [treeAt_succ_pair W step f k i0]
  have hpair : ∀ i, f i + (f (i + step) <<< W) < 2 ^ (W * 2) := by
    intro i
    rw [Nat.shiftLeft_eq]
    have hfi : f i < 2 ^ W := Nat.lt_of_lt_of_le (hf i) (Nat.pow_le_pow_right (by omega) (by omega))
    have hcomb := add_mul_two_pow_lt hfi (hf (i + step))
    exact Nat.lt_of_lt_of_le hcomb (Nat.pow_le_pow_right (by omega) (by omega))
  have hmask : ∀ (_ : Nat), 2 ^ (B + B) - 1 < 2 ^ (W * 2 - s) := by
    intro _
    have hle : B + B ≤ W * 2 - s := by omega
    have hpow : 2 ^ (B + B) ≤ 2 ^ (W * 2 - s) := Nat.pow_le_pow_right (by omega) hle
    have hpos : 1 ≤ 2 ^ (B + B) := Nat.one_le_two_pow
    omega
  have hmask0 : ∀ (_ : Nat), 2 ^ (B + B) - 1 < 2 ^ (W * 2) := by
    intro i
    exact Nat.lt_of_lt_of_le (hmask i) (Nat.pow_le_pow_right (by omega) (by omega))
  rw [Nat.and_or_distrib_right,
      treeAt_and (W * 2) (step * 2) hpair hmask0,
      treeAt_shr_and (W * 2) (step * 2) s (by omega) hpair hmask,
      treeAt_or (W * 2) (step * 2)
        (fun i => Nat.lt_of_le_of_lt Nat.and_le_right (hmask0 i))
        (fun i => Nat.lt_of_le_of_lt Nat.and_le_right (hmask0 i))]
  apply treeAt_congr
  intro i
  rw [← Nat.and_or_distrib_right]
  exact butterfly_leaf hW hBW (hf i) (hf (i + step))

theorem treeAt_butterfly_step (W step B s r : Nat)
    (hstep : step = 1 * 2 ^ r) (hB : B = 1 * 2 ^ r)
    (hW : W = s + B) (hBW : B + B ≤ W)
    {{g : Nat → Nat}} (hg : ∀ i, treeAt 1 1 r g i < 2 ^ B) (k i0 : Nat) :
    ((treeAt W step (k + 1) (treeAt 1 1 r g) i0 ||| (treeAt W step (k + 1) (treeAt 1 1 r g) i0 >>> s)) &&&
      treeAt (W * 2) (step * 2) k (fun _ => 2 ^ (B + B) - 1) i0) =
    treeAt (W * 2) (step * 2) k (treeAt 1 1 (r + 1) g) i0 := by
  rw [treeAt_butterfly W step B s hW hBW hg k i0]
  apply treeAt_congr
  intro i
  simp only [treeAt, hstep, hB]

theorem treeAt_one_eq_encodeRow (f : Nat → Bool) :
    ∀ k i0, treeAt 1 1 k (fun i => if f i then 1 else 0) i0 =
      encodeRow ((List.range (2 ^ k)).map (fun j => f (i0 + j)))
  | 0, i0 => by
    have h : List.range (2 ^ 0) = [0] := rfl
    rw [h]
    simp [treeAt, encodeRow]
  | k + 1, i0 => by
    simp only [treeAt, Nat.one_mul]
    rw [treeAt_one_eq_encodeRow f k i0, treeAt_one_eq_encodeRow f k (i0 + 2 ^ k)]
    have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
    rw [hpow, List.range_add, List.map_append, encodeRow_append, List.length_map, List.length_range,
        List.map_map]
    congr 3
    apply List.map_congr_left
    intro j _; dsimp; congr 1; omega

/-! ### Part 3: 64-bit SWAR initialization proof -/

def w32 : Nat := 0xffffffff
def m1 : Nat := 0x7feb352d
def m2 : Nat := 0x846ca68b

theorem and_w32_eq_mod (x : Nat) : (x &&& w32) = x % 2 ^ 32 := by
  change x &&& (2 ^ 32 - 1) = x % 2 ^ 32
  exact Nat.and_two_pow_sub_one_eq_mod x 32

theorem and_w32_lt (x : Nat) : (x &&& w32) < 2 ^ 32 := by
  rw [and_w32_eq_mod]
  exact Nat.mod_lt x (by decide)

theorem mul_and_w32 (a c : Nat) : (((a &&& w32) * c) &&& w32) = ((a * c) &&& w32) := by
  rw [and_w32_eq_mod, and_w32_eq_mod, and_w32_eq_mod, Nat.mod_mul_mod]

theorem shr31_and1_w32 (z : Nat) : ((z >>> 31) &&& 1) = (((z &&& w32) >>> 31) &&& 1) := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_and, Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_shiftRight, Nat.testBit_and]
  by_cases hj0 : j = 0
  · subst hj0
    have hw : w32.testBit 31 = true := by decide
    simp [hw]
  · have h1j : (1 : Nat).testBit j = false := testBit_high (W := 1) (by decide) (by omega)
    simp [h1j]

theorem mix_final_bit31 {{x : Nat}} (hx : x < 2 ^ 32) :
    ((x >>> 31) &&& 1) = (if (((x ^^^ (x >>> 16)) &&& w32).testBit 31) then 1 else 0) := by
  have hhi : (x >>> 16).testBit 31 = false := by
    rw [Nat.testBit_shiftRight]
    exact testBit_high hx (by omega)
  have h31 : (((x ^^^ (x >>> 16)) &&& w32).testBit 31) = x.testBit 31 := by
    have hw : w32.testBit 31 = true := by decide
    rw [Nat.testBit_and, Nat.testBit_xor, hhi, hw, Bool.xor_false, Bool.and_true]
  rw [h31]
  show ((x >>> 31) &&& 1) = if ((1 &&& (x >>> 31)) != 0) then 1 else 0
  rw [Nat.and_comm]
  have hle : 1 &&& (x >>> 31) ≤ 1 := Nat.and_le_left
  generalize 1 &&& (x >>> 31) = b at hle
  match b with
  | 0 => rfl
  | 1 => rfl
  | n + 2 => omega

theorem leaf_mix_eq_x0 (x0 : Nat) :
    ((((((((x0 ^^^ (x0 >>> 16)) &&& w32) * m1) &&& w32) ^^^
       (((((x0 ^^^ (x0 >>> 16)) &&& w32) * m1) &&& w32) >>> 15)) &&& w32) * m2) >>> 31) &&& 1 =
      (if (caMix32 x0).testBit 31 then 1 else 0) := by
  rw [mul_and_w32 (x0 ^^^ (x0 >>> 16)) m1]
  rw [shr31_and1_w32]
  rw [mul_and_w32 _ m2]
  exact mix_final_bit31 (and_w32_lt _)

def repF (i : Nat) : Nat := if 2 ≤ i ∧ i < 256 then 1 else 0
def offF (i : Nat) : Nat := if 2 ≤ i ∧ i < 256 then (i + 1) * 0x9e3779b9 else 0
def mask32F (i : Nat) : Nat := if 2 ≤ i ∧ i < 256 then w32 else 0
def bit0F (i : Nat) : Nat := if i = 0 then 1 else 0

def cellBool (seed i : Nat) : Bool :=
  if i = 0 then true
  else if i = 1 then false
  else (caMix32 (seed + (i + 1) * 0x9e3779b9)).testBit 31

def cellNat (seed i : Nat) : Nat := if cellBool seed i then 1 else 0

def rep64Lit : Nat := (nat_lit {REP_64_2})
def off64Lit : Nat := (nat_lit {OFFSETS_64_2})
def mask32Lit : Nat := (nat_lit {MASK32_64_2})
def m1R : Nat := (nat_lit {M1})
def m2R : Nat := (nat_lit {M2})
def w32R : Nat := (nat_lit {W32})
def MRaw : Nat := (nat_lit {M256})
def rep3Lit : Nat := (nat_lit {REP3_256})

{bf_defs_str}

theorem rep64Lit_eq : rep64Lit = treeAt 64 1 8 repF 0 := rfl
theorem off64Lit_eq : off64Lit = treeAt 64 1 8 offF 0 := rfl
theorem mask32Lit_eq : mask32Lit = treeAt 64 1 8 mask32F 0 := rfl
theorem bit0Lit_eq : (1 : Nat) = treeAt 64 1 8 bit0F 0 := rfl
theorem bfMask0_eq : bfMask0 = treeAt 128 2 7 (fun _ => 2 ^ 2 - 1) 0 := rfl
theorem bfMask1_eq : bfMask1 = treeAt 256 4 6 (fun _ => 2 ^ 4 - 1) 0 := rfl
theorem bfMask2_eq : bfMask2 = treeAt 512 8 5 (fun _ => 2 ^ 8 - 1) 0 := rfl
theorem bfMask3_eq : bfMask3 = treeAt 1024 16 4 (fun _ => 2 ^ 16 - 1) 0 := rfl
theorem bfMask4_eq : bfMask4 = treeAt 2048 32 3 (fun _ => 2 ^ 32 - 1) 0 := rfl
theorem bfMask5_eq : bfMask5 = treeAt 4096 64 2 (fun _ => 2 ^ 64 - 1) 0 := rfl
theorem bfMask6_eq : bfMask6 = treeAt 8192 128 1 (fun _ => 2 ^ 128 - 1) 0 := rfl
theorem bfMask7_eq : bfMask7 = treeAt 16384 256 0 (fun _ => 2 ^ 256 - 1) 0 := rfl

theorem hand_eq (x y : Nat) : Nat.land x y = (x &&& y) := rfl
theorem hxor_eq (x y : Nat) : Nat.xor x y = (x ^^^ y) := rfl
theorem hor_eq (x y : Nat) : Nat.lor x y = (x ||| y) := rfl
theorem hshl_eq (x y : Nat) : Nat.shiftLeft x y = (x <<< y) := rfl
theorem hshr_eq (x y : Nat) : Nat.shiftRight x y = (x >>> y) := rfl
theorem hadd_eq (x y : Nat) : Nat.add x y = (x + y) := rfl
theorem hmul_eq (x y : Nat) : Nat.mul x y = (x * y) := rfl
theorem hsub_eq (x y : Nat) : Nat.sub x y = (x - y) := rfl

def initBitsSwar (seed : Nat) : Nat :=
  let x := Nat.add (Nat.mul seed (nat_lit {REP_64_2})) (nat_lit {OFFSETS_64_2})
  let x := Nat.land (Nat.xor x (Nat.shiftRight x (nat_lit 16))) (nat_lit {MASK32_64_2})
  let x := Nat.land (Nat.mul x (nat_lit {M1})) (nat_lit {MASK32_64_2})
  let x := Nat.land (Nat.xor x (Nat.shiftRight x (nat_lit 15))) (nat_lit {MASK32_64_2})
  let b := Nat.lor (Nat.land (Nat.shiftRight (Nat.mul x (nat_lit {M2})) (nat_lit 31)) (nat_lit {REP_64_2})) (nat_lit 1)
{bf_lets_str}
  b

def f0 (seed i : Nat) : Nat := repF i * seed + offF i
def f1 (seed i : Nat) : Nat := ((f0 seed i &&& mask32F i) ^^^ ((f0 seed i >>> 16) &&& mask32F i))
def f2 (seed i : Nat) : Nat := (f1 seed i * m1) &&& mask32F i
def f3 (seed i : Nat) : Nat := ((f2 seed i &&& mask32F i) ^^^ ((f2 seed i >>> 15) &&& mask32F i))
def f4 (seed i : Nat) : Nat := (((f3 seed i * m2) >>> 31) &&& repF i) ||| bit0F i

theorem mask32F_lt (i : Nat) : mask32F i < 2 ^ 32 := by
  unfold mask32F w32; split <;> omega

theorem mask32F_lt48 (i : Nat) : mask32F i < 2 ^ (64 - 16) := by
  have := mask32F_lt i; omega

theorem mask32F_lt49 (i : Nat) : mask32F i < 2 ^ (64 - 15) := by
  have := mask32F_lt i; omega

theorem mask32F_lt64 (i : Nat) : mask32F i < 2 ^ 64 := by
  have := mask32F_lt i; omega

theorem repF_lt33 (i : Nat) : repF i < 2 ^ (64 - 31) := by
  unfold repF; split <;> omega

theorem repF_lt64 (i : Nat) : repF i < 2 ^ 64 := by
  unfold repF; split <;> omega

theorem bit0F_lt64 (i : Nat) : bit0F i < 2 ^ 64 := by
  unfold bit0F; split <;> omega

theorem f0_lt64 {{seed : Nat}} (hseed : seed < 2 ^ 32) (i : Nat) : f0 seed i < 2 ^ 64 := by
  unfold f0 repF offF
  split <;> omega

theorem f1_lt32 (seed i : Nat) : f1 seed i < 2 ^ 32 := by
  unfold f1
  exact Nat.xor_lt_two_pow
    (Nat.lt_of_le_of_lt Nat.and_le_right (mask32F_lt i))
    (Nat.lt_of_le_of_lt Nat.and_le_right (mask32F_lt i))

theorem f1_mul_lt64 (seed i : Nat) : f1 seed i * m1 < 2 ^ 64 := by
  have := f1_lt32 seed i
  unfold m1; omega

theorem f2_lt32 (seed i : Nat) : f2 seed i < 2 ^ 32 := by
  unfold f2
  exact Nat.lt_of_le_of_lt Nat.and_le_right (mask32F_lt i)

theorem f2_lt64 (seed i : Nat) : f2 seed i < 2 ^ 64 := by
  have := f2_lt32 seed i; omega

theorem f3_lt32 (seed i : Nat) : f3 seed i < 2 ^ 32 := by
  unfold f3
  exact Nat.xor_lt_two_pow
    (Nat.lt_of_le_of_lt Nat.and_le_right (mask32F_lt i))
    (Nat.lt_of_le_of_lt Nat.and_le_right (mask32F_lt i))

theorem f3_mul_lt64 (seed i : Nat) : f3 seed i * m2 < 2 ^ 64 := by
  have := f3_lt32 seed i
  unfold m2; omega

theorem cellNat_lt (seed i : Nat) : treeAt 1 1 0 (cellNat seed) i < 2 ^ 1 := by
  simp only [treeAt, cellNat]; split <;> omega

theorem treeAt_one_lt (seed k i : Nat) : treeAt 1 1 k (cellNat seed) i < 2 ^ (1 * 2 ^ k) :=
  treeAt_lt0 1 1 (cellNat_lt seed) k i

theorem f4_eq_cellNat (seed i : Nat) (hi : i < 256) : f4 seed i = cellNat seed i := by
  by_cases hi0 : i = 0
  · subst hi0
    simp [f4, f3, f2, f1, f0, repF, offF, mask32F, bit0F, cellNat, cellBool]
  · by_cases hi1 : i = 1
    · subst hi1
      simp [f4, f3, f2, f1, f0, repF, offF, mask32F, bit0F, cellNat, cellBool]
    · have hact : 2 ≤ i ∧ i < 256 := ⟨by omega, hi⟩
      have hb0 : bit0F i = 0 := by unfold bit0F; rw [if_neg hi0]
      have hrep : repF i = 1 := by unfold repF; rw [if_pos hact]
      have hoff : offF i = (i + 1) * 0x9e3779b9 := by unfold offF; rw [if_pos hact]
      have hmsk : mask32F i = w32 := by unfold mask32F; rw [if_pos hact]
      unfold f4 f3 f2 f1 f0 cellNat cellBool
      rw [hrep, hoff, hmsk, hb0, if_neg hi0, if_neg hi1]
      simp only [Nat.one_mul, Nat.or_zero, ← Nat.and_xor_distrib_right]
      exact leaf_mix_eq_x0 (seed + (i + 1) * 0x9e3779b9)

theorem treeAt_zero (W step : Nat) (f : Nat → Nat) (i0 : Nat) :
    treeAt W step 0 f i0 = f i0 := rfl

theorem initBitsSwar_eq_spec {{seed : Nat}} (hseed : seed < 2 ^ 32) :
    initBitsSwar seed = encodeRow (initRowFor seed) := by
  unfold initBitsSwar
  dsimp only
  simp only [hand_eq, hxor_eq, hor_eq, hshr_eq, hadd_eq, hmul_eq]
  change (let x0 := seed * rep64Lit + off64Lit
          let x1 := (x0 ^^^ (x0 >>> 16)) &&& mask32Lit
          let x2 := (x1 * m1) &&& mask32Lit
          let x3 := (x2 ^^^ (x2 >>> 15)) &&& mask32Lit
          let b0 := (((x3 * m2) >>> 31) &&& rep64Lit) ||| 1
          let b1 := (b0 ||| (b0 >>> 63)) &&& bfMask0
          let b2 := (b1 ||| (b1 >>> 126)) &&& bfMask1
          let b3 := (b2 ||| (b2 >>> 252)) &&& bfMask2
          let b4 := (b3 ||| (b3 >>> 504)) &&& bfMask3
          let b5 := (b4 ||| (b4 >>> 1008)) &&& bfMask4
          let b6 := (b5 ||| (b5 >>> 2016)) &&& bfMask5
          let b7 := (b6 ||| (b6 >>> 4032)) &&& bfMask6
          (b7 ||| (b7 >>> 8064)) &&& bfMask7) = encodeRow (initRowFor seed)
  have hx0 : seed * rep64Lit + off64Lit = treeAt 64 1 8 (f0 seed) 0 := by
    rw [rep64Lit_eq, off64Lit_eq, Nat.mul_comm seed, treeAt_mul, treeAt_add]; rfl
  have hx1 : ((treeAt 64 1 8 (f0 seed) 0 ^^^ (treeAt 64 1 8 (f0 seed) 0 >>> 16)) &&& mask32Lit) =
      treeAt 64 1 8 (f1 seed) 0 := by
    rw [mask32Lit_eq, Nat.and_xor_distrib_right,
        treeAt_and 64 1 (f0_lt64 hseed) mask32F_lt64,
        treeAt_shr_and 64 1 16 (by omega) (f0_lt64 hseed) mask32F_lt48,
        treeAt_xor 64 1
          (fun i => Nat.lt_of_le_of_lt Nat.and_le_right (mask32F_lt64 i))
          (fun i => Nat.lt_of_le_of_lt Nat.and_le_right (mask32F_lt64 i))]; rfl
  have hx2 : ((treeAt 64 1 8 (f1 seed) 0 * m1) &&& mask32Lit) = treeAt 64 1 8 (f2 seed) 0 := by
    rw [mask32Lit_eq, treeAt_mul, treeAt_and 64 1 (f1_mul_lt64 seed) mask32F_lt64]; rfl
  have hx3 : ((treeAt 64 1 8 (f2 seed) 0 ^^^ (treeAt 64 1 8 (f2 seed) 0 >>> 15)) &&& mask32Lit) =
      treeAt 64 1 8 (f3 seed) 0 := by
    rw [mask32Lit_eq, Nat.and_xor_distrib_right,
        treeAt_and 64 1 (f2_lt64 seed) mask32F_lt64,
        treeAt_shr_and 64 1 15 (by omega) (f2_lt64 seed) mask32F_lt49,
        treeAt_xor 64 1
          (fun i => Nat.lt_of_le_of_lt Nat.and_le_right (mask32F_lt64 i))
          (fun i => Nat.lt_of_le_of_lt Nat.and_le_right (mask32F_lt64 i))]; rfl
  have hb0_shr : (((treeAt 64 1 8 (f3 seed) 0 * m2) >>> 31) &&& rep64Lit) =
      treeAt 64 1 8 (fun i => ((f3 seed i * m2) >>> 31) &&& repF i) 0 := by
    rw [rep64Lit_eq, treeAt_mul, treeAt_shr_and 64 1 31 (by omega) (f3_mul_lt64 seed) repF_lt33]
  have hb0 : ((((treeAt 64 1 8 (f3 seed) 0 * m2) >>> 31) &&& rep64Lit) ||| 1) =
      treeAt 64 1 8 (treeAt 1 1 0 (cellNat seed)) 0 := by
    rw [hb0_shr]
    conv => lhs; rhs; rw [bit0Lit_eq]
    rw [treeAt_or 64 1
          (fun i => Nat.lt_of_le_of_lt Nat.and_le_right (repF_lt64 i))
          bit0F_lt64]
    exact treeAt_bound_congr 64 1 (by omega) 8 0 (fun i hi => f4_eq_cellNat seed i (by simpa using hi))
  dsimp only
  rw [hx0, hx1, hx2, hx3, hb0]
  rw [bfMask0_eq, treeAt_butterfly_step 64 1 1 63 0 rfl rfl (by omega) (by omega) (treeAt_one_lt seed 0) 7 0]
  rw [bfMask1_eq, treeAt_butterfly_step 128 2 2 126 1 rfl rfl (by omega) (by omega) (treeAt_one_lt seed 1) 6 0]
  rw [bfMask2_eq, treeAt_butterfly_step 256 4 4 252 2 rfl rfl (by omega) (by omega) (treeAt_one_lt seed 2) 5 0]
  rw [bfMask3_eq, treeAt_butterfly_step 512 8 8 504 3 rfl rfl (by omega) (by omega) (treeAt_one_lt seed 3) 4 0]
  rw [bfMask4_eq, treeAt_butterfly_step 1024 16 16 1008 4 rfl rfl (by omega) (by omega) (treeAt_one_lt seed 4) 3 0]
  rw [bfMask5_eq, treeAt_butterfly_step 2048 32 32 2016 5 rfl rfl (by omega) (by omega) (treeAt_one_lt seed 5) 2 0]
  rw [bfMask6_eq, treeAt_butterfly_step 4096 64 64 4032 6 rfl rfl (by omega) (by omega) (treeAt_one_lt seed 6) 1 0]
  rw [bfMask7_eq, treeAt_butterfly_step 8192 128 128 8064 7 rfl rfl (by omega) (by omega) (treeAt_one_lt seed 7) 0 0]
  rw [treeAt_zero]
  unfold cellNat
  rw [treeAt_one_eq_encodeRow (cellBool seed) 8 0]
  unfold initRowFor cellBool ruleWidth
  simp only [Nat.zero_add]

/-! ### Part 4: 6-Op Lightcone Step & Dispatch Proof -/

def sstep (m : Nat) : Nat :=
  let c := m >>> 1
  let r := m >>> 2
  (c ||| r) ^^^ (m &&& (c &&& r))

theorem testBit_sstep (m i : Nat) :
    (sstep m).testBit i = rule110 (m.testBit i) (m.testBit (i + 1)) (m.testBit (i + 2)) := by
  unfold sstep
  dsimp only
  rw [Nat.testBit_xor, Nat.testBit_or, Nat.testBit_and, Nat.testBit_and,
      Nat.testBit_shiftRight, Nat.testBit_shiftRight]
  rw [Nat.add_comm 1 i, Nat.add_comm 2 i]
  generalize m.testBit i = a
  generalize m.testBit (i + 1) = b
  generalize m.testBit (i + 2) = c
  cases a <;> cases b <;> cases c <;> decide

def ValidAt (m o L : Nat) (row : List Bool) : Prop :=
  row.length = 256 ∧ o ≤ 8 ∧ ∀ i < L, m.testBit i = row.getD ((i + 256 - o) % 256) false

theorem validAt_sstep {{m o L : Nat}} {{row : List Bool}}
    (hv : ValidAt m (o + 1) (L + 2) row) :
    ValidAt (sstep m) o L (stepRow row) := by
  rcases hv with ⟨hlen, ho, hbit⟩
  refine ⟨by rw [length_stepRow, hlen], by omega, ?_⟩
  intro i hi
  rw [testBit_sstep, hbit i (by omega), hbit (i + 1) (by omega), hbit (i + 2) (by omega),
      getD_stepRow, hlen]
  have hlt : (i + 256 - o) % 256 < 256 := Nat.mod_lt _ (by decide)
  rw [if_pos hlt]
  have e1 : (i + 256 - (o + 1)) % 256 = ((i + 256 - o) % 256 + 256 - 1) % 256 := by omega
  have e2 : (i + 1 + 256 - (o + 1)) % 256 = (i + 256 - o) % 256 := by omega
  have e3 : (i + 2 + 256 - (o + 1)) % 256 = ((i + 256 - o) % 256 + 1) % 256 := by omega
  rw [e1, e2, e3]

def rep3 : Nat := 1 + ((1 + (1 <<< 256)) <<< 256)
theorem rep3Lit_eq : rep3Lit = rep3 := rfl
theorem MRaw_eq : MRaw = M := rfl

theorem validAt_init {{row : List Bool}} (hlen : row.length = 256) :
    ValidAt (((encodeRow row) * rep3) >>> 248) 8 272 row := by
  refine ⟨hlen, by omega, ?_⟩
  intro i hi
  have hb : encodeRow row < 2 ^ 256 := hlen ▸ encodeRow_lt row
  have hrep : encodeRow row * rep3 = encodeRow row + ((encodeRow row + (encodeRow row <<< 256)) <<< 256) := by
    unfold rep3
    rw [Nat.mul_comm (encodeRow row), pack_mul 256 1 (1 + (1 <<< 256)) (encodeRow row),
        Nat.one_mul, pack_mul 256 1 1 (encodeRow row), Nat.one_mul]
  rw [Nat.testBit_shiftRight, hrep, testBit_pack hb]
  by_cases h1 : 248 + i < 256
  · rw [if_pos h1, testBit_encodeRow]
    have heq : 248 + i = (i + 256 - 8) % 256 := by omega
    rw [heq]
  · rw [if_neg h1, testBit_pack hb]
    by_cases h2 : 248 + i - 256 < 256
    · rw [if_pos h2, testBit_encodeRow]
      have heq : 248 + i - 256 = (i + 256 - 8) % 256 := by omega
      rw [heq]
    · rw [if_neg h2, testBit_encodeRow]
      have heq : 248 + i - 256 - 256 = (i + 256 - 8) % 256 := by omega
      rw [heq]

theorem validAt_extract {{m o L : Nat}} {{row : List Bool}}
    (hv : ValidAt m o L row) (hL : o + 256 ≤ L) :
    ((m >>> o) &&& M) = encodeRow row := by
  rcases hv with ⟨hlen, ho, hbit⟩
  have hrow : encodeRow row < 2 ^ 256 := hlen ▸ encodeRow_lt row
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_and, Nat.testBit_shiftRight, testBit_M]
  by_cases hi : i < 256
  · simp only [hi, decide_true, Bool.and_true]
    rw [hbit (o + i) (by omega), testBit_encodeRow]
    have heq : (o + i + 256 - o) % 256 = i := by omega
    rw [heq]
  · simp only [hi, decide_false, Bool.and_false]
    exact (testBit_high hrow (by omega)).symm

theorem validAt_extract0 {{m L : Nat}} {{row : List Bool}}
    (hv : ValidAt m 0 L row) (hL : 256 ≤ L) :
    (m &&& M) = encodeRow row := by
  have h := validAt_extract hv (by omega)
  simpa using h

def bstepRaw (m0 : Nat) : Nat :=
  let r := Nat.lor (Nat.shiftRight m0 (nat_lit 1)) (Nat.shiftLeft (Nat.land m0 (nat_lit 1)) (nat_lit 255))
  let l := Nat.lor (Nat.shiftLeft m0 (nat_lit 1)) (Nat.shiftRight m0 (nat_lit 255))
  Nat.xor (Nat.lor m0 r) (Nat.land l (Nat.land m0 r))

theorem bstepRaw_eq (m : Nat) : bstepRaw m = bstep m := rfl

def sstepRaw (m0 : Nat) : Nat :=
  let c := Nat.shiftRight m0 (nat_lit 1)
  let r := Nat.shiftRight m0 (nat_lit 2)
  Nat.xor (Nat.lor c r) (Nat.land m0 (Nat.land c r))

theorem sstepRaw_eq (m : Nat) : sstepRaw m = sstep m := rfl

noncomputable def biterRaw (t : Nat) : Nat → Nat :=
  @Nat.rec (fun _ => Nat → Nat) (fun m => m)
    (fun _ f => fun m => f (bstepRaw m)) t

theorem biterRaw_eq : ∀ t m, biterRaw t m = biter t m := by
  intro t; induction t with
  | zero => intro m; rfl
  | succ k ih =>
    intro m
    show biterRaw k (bstepRaw m) = biter k (bstep m)
    rw [bstepRaw_eq, ih]

theorem beq_true_eq {{x y : Nat}} (h : Nat.beq x y = true) : x = y :=
  Nat.eq_of_beq_eq_true h

noncomputable def impl (n : Nat) : Nat :=
  let t := Nat.shiftRight n (nat_lit 32)
  let b := initBitsSwar (Nat.land n (nat_lit {W32}))
  let m := Nat.shiftRight (Nat.mul b (nat_lit {REP3_256})) (nat_lit 248)
  let m2 := sstepRaw (sstepRaw m)
  @Bool.rec (fun _ => Nat)
    (let m4 := sstepRaw (sstepRaw m2)
     @Bool.rec (fun _ => Nat)
       (@Bool.rec (fun _ => Nat)
         (biterRaw t b)
         (Nat.land (sstepRaw (sstepRaw (sstepRaw (sstepRaw m4)))) (nat_lit {M256}))
         (Nat.beq t (nat_lit 8)))
       (Nat.land (Nat.shiftRight m4 (nat_lit 4)) (nat_lit {M256}))
       (Nat.beq t (nat_lit 4)))
    (Nat.land (Nat.shiftRight m2 (nat_lit 6)) (nat_lit {M256}))
    (Nat.beq t (nat_lit 2))

theorem impl_correct : ∀ n, impl n = caSpecN n := by
  intro n
  unfold impl caSpecN
  dsimp only
  have hseed_eq : Nat.land n (nat_lit {W32}) = caSeed n := rfl
  have hsteps_eq : Nat.shiftRight n (nat_lit 32) = caSteps n := rfl
  rw [hseed_eq, hsteps_eq]
  have hseed_lt : caSeed n < 2 ^ 32 := and_w32_lt n
  rw [initBitsSwar_eq_spec hseed_lt]
  simp only [sstepRaw_eq]
  let row := initRowFor (caSeed n)
  have hlen : row.length = 256 := by simp [row, initRowFor, ruleWidth]
  have hv0 : ValidAt (Nat.shiftRight (Nat.mul (encodeRow row) (nat_lit {REP3_256})) (nat_lit 248)) 8 272 row := by
    change ValidAt (Nat.shiftRight (Nat.mul (encodeRow row) rep3Lit) (nat_lit 248)) 8 272 row
    rw [hmul_eq, hshr_eq, rep3Lit_eq]
    exact validAt_init hlen
  have hv2 : ValidAt (sstep (sstep (Nat.shiftRight (Nat.mul (encodeRow row) (nat_lit {REP3_256})) (nat_lit 248)))) 6 268 (iterRow 2 row) :=
    validAt_sstep (validAt_sstep hv0)
  cases h2 : Nat.beq (caSteps n) (nat_lit 2)
  · dsimp only
    have hv4 := validAt_sstep (validAt_sstep hv2)
    cases h4 : Nat.beq (caSteps n) (nat_lit 4)
    · dsimp only
      have hv8 := validAt_sstep (validAt_sstep (validAt_sstep (validAt_sstep hv4)))
      cases h8 : Nat.beq (caSteps n) (nat_lit 8)
      · dsimp only
        rw [biterRaw_eq, iter_eq (caSteps n) row hlen]
      · dsimp only
        have ht8 : caSteps n = 8 := beq_true_eq h8
        change Nat.land _ MRaw = _
        rw [ht8, hand_eq, MRaw_eq]
        exact validAt_extract0 hv8 (by omega)
    · dsimp only
      have ht4 : caSteps n = 4 := beq_true_eq h4
      change Nat.land _ MRaw = _
      rw [ht4, hand_eq, hshr_eq, MRaw_eq]
      exact validAt_extract hv4 (by omega)
  · dsimp only
    have ht2 : caSteps n = 2 := beq_true_eq h2
    change Nat.land _ MRaw = _
    rw [ht2, hand_eq, hshr_eq, MRaw_eq]
    exact validAt_extract hv2 (by omega)

end Submission
"""

DST.write_text(src)
print(f"wrote {DST} ({len(src)} bytes)")
