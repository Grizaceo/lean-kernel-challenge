#!/usr/bin/env python3
"""Generate candidates/ca-rule110-v4/Submission.lean.

v4 = Bit-parallel Rule 110 with 100% raw kernel primitives on the hot path (F16 rule):
  1. `initBitsRaw`: 256-cell unrolled initialization with `caMix32Raw` inlined via
     `let` bindings, precomputed `(i + 1) * 0x9e3779b9` offsets as `(nat_lit ...)`,
     and bit-31 extraction via `Nat.land (nat_lit 1) (Nat.shiftRight x (nat_lit 31))`
     (eliminating 254 calls to `Nat.testBit`, `@bne`, `instDecidableEqNat`, `@ite`,
     and all typeclass projections inside `caMix32`).
  2. `bstepRaw`, `biterRaw`, `caStepsRaw`, `caSeedRaw`: raw `Nat.land`, `Nat.lor`,
     `Nat.xor`, `Nat.shiftLeft`, `Nat.shiftRight`, `(nat_lit ...)` and `@Nat.rec`.
  3. Fast O(256) proof via functional abstraction `initUnrolledG_eq` (`rfl` on
     opaque function variables `stepF` and `cellF` in < 0.5s, avoiding exponential
     `Nat.mul` unfolding in `isDefEq`) + list induction `foldr_cell_eq`.
"""
from pathlib import Path

DST = Path(__file__).resolve().parent / "Submission.lean"

K = 0x9e3779b9
W32 = "(nat_lit 4294967295)"
M1 = "(nat_lit 2146121005)"
M2 = "(nat_lit 2221713035)"


def cell_inlined_s(seed_expr: str, i: int) -> str:
    if i == 0:
        return "(nat_lit 1)"
    if i == 1:
        return "(nat_lit 0)"
    offset = (i + 1) * K
    x0 = f"(Nat.add {seed_expr} (nat_lit {offset}))"
    return (
        f"(let x := {x0}; "
        f"let x := Nat.land (Nat.mul (Nat.xor x (Nat.shiftRight x (nat_lit 16))) {M1}) {W32}; "
        f"let x := Nat.land (Nat.mul (Nat.xor x (Nat.shiftRight x (nat_lit 15))) {M2}) {W32}; "
        f"let x := Nat.land (Nat.xor x (Nat.shiftRight x (nat_lit 16))) {W32}; "
        f"Nat.land (nat_lit 1) (Nat.shiftRight x (nat_lit 31)))"
    )


def main() -> None:
    g_acc = "z"
    r_acc = "(nat_lit 0)"
    for i in range(255, -1, -1):
        cs = cell_inlined_s("seed", i)
        g_acc = f"stepF (cellF (nat_lit {i})) ({g_acc})"
        r_acc = f"Nat.add (Nat.mul (nat_lit 2) ({r_acc})) {cs}"

    src = f"""import Spec

namespace Submission

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! ### Trusted spec facts (as in the official example) -/

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

@[simp] theorem length_stepRow (row : List Bool) : (stepRow row).length = row.length := by
  simp [stepRow]

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

/-! ### Bit-parallel reference kernel -/

def M : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
theorem M_eq : M = 2 ^ 256 - 1 := by decide
theorem testBit_M (i : Nat) : M.testBit i = decide (i < 256) := by
  rw [M_eq, Nat.testBit_two_pow_sub_one]
theorem testBit_high {{m : Nat}} (hm : m < 2 ^ 256) {{j : Nat}} (hj : 256 ≤ j) : m.testBit j = false := by
  have hlt : m < 2 ^ j := Nat.lt_of_lt_of_le hm (Nat.pow_le_pow_right (by omega) hj)
  simp [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hlt]

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
  (M ^^^ (((M ^^^ m) &&& (M ^^^ (((m >>> 1) ||| ((m &&& 1) <<< 255)) &&& M))) |||
          ((((m <<< 1) ||| (m >>> 255)) &&& M) &&& m &&& (((m >>> 1) ||| ((m &&& 1) <<< 255)) &&& M)))) &&& M

def biter : Nat → Nat → Nat
  | 0, m => m
  | t + 1, m => biter t (bstep m)

/-! ### Raw kernel primitives — v4 (F16 rule) -/

def MRaw : Nat := (nat_lit 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)
def w32R : Nat := (nat_lit 0xffffffff)
def m1R : Nat := (nat_lit 0x7feb352d)
def m2R : Nat := (nat_lit 0x846ca68b)
def cK : Nat := (nat_lit 0x9e3779b9)

theorem hand_eq (x y : Nat) : (x &&& y) = Nat.land x y := rfl
theorem hxor_eq (x y : Nat) : (x ^^^ y) = Nat.xor x y := rfl
theorem hor_eq (x y : Nat) : (x ||| y) = Nat.lor x y := rfl
theorem hshl_eq (x y : Nat) : (x <<< y) = Nat.shiftLeft x y := rfl
theorem hshr_eq (x y : Nat) : (x >>> y) = Nat.shiftRight x y := rfl
theorem hadd_eq (x y : Nat) : (x + y) = Nat.add x y := rfl
theorem hmul_eq (x y : Nat) : (x * y) = Nat.mul x y := rfl
theorem MRaw_eq : M = MRaw := rfl
theorem w32R_eq : (0xffffffff : Nat) = w32R := rfl
theorem m1R_eq : (0x7feb352d : Nat) = m1R := rfl
theorem m2R_eq : (0x846ca68b : Nat) = m2R := rfl
theorem cK_eq : (0x9e3779b9 : Nat) = cK := rfl

def bstepRaw (m : Nat) : Nat :=
  Nat.land
    (Nat.xor MRaw
      (Nat.lor
        (Nat.land (Nat.xor MRaw m)
          (Nat.xor MRaw
            (Nat.land
              (Nat.lor (Nat.shiftRight m (nat_lit 1))
                       (Nat.shiftLeft (Nat.land m (nat_lit 1)) (nat_lit 255)))
              MRaw)))
        (Nat.land
          (Nat.land
            (Nat.land
              (Nat.lor (Nat.shiftLeft m (nat_lit 1)) (Nat.shiftRight m (nat_lit 255)))
              MRaw)
            m)
          (Nat.land
            (Nat.lor (Nat.shiftRight m (nat_lit 1))
                     (Nat.shiftLeft (Nat.land m (nat_lit 1)) (nat_lit 255)))
            MRaw))))
    MRaw

theorem bstepRaw_eq (m : Nat) : bstepRaw m = bstep m := by
  unfold bstepRaw bstep
  simp only [hand_eq, hxor_eq, hor_eq, hshl_eq, hshr_eq, MRaw_eq]

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

def caStepsRaw (n : Nat) : Nat := Nat.shiftRight n (nat_lit 32)
theorem caStepsRaw_eq (n : Nat) : caStepsRaw n = caSteps n := by
  unfold caStepsRaw caSteps; simp only [hshr_eq]

def caSeedRaw (n : Nat) : Nat := Nat.land n w32R
theorem caSeedRaw_eq (n : Nat) : caSeedRaw n = caSeed n := by
  unfold caSeedRaw caSeed; simp only [hand_eq, w32R_eq]

def caMix32Raw (x : Nat) : Nat :=
  let x := Nat.land (Nat.mul (Nat.xor x (Nat.shiftRight x (nat_lit 16))) m1R) w32R
  let x := Nat.land (Nat.mul (Nat.xor x (Nat.shiftRight x (nat_lit 15))) m2R) w32R
  Nat.land (Nat.xor x (Nat.shiftRight x (nat_lit 16))) w32R

theorem caMix32Raw_eq (x : Nat) : caMix32Raw x = caMix32 x := by
  unfold caMix32Raw caMix32
  simp only [hand_eq, hxor_eq, hshr_eq, hmul_eq, w32R_eq, m1R_eq, m2R_eq]

def cellBitRaw (x : Nat) : Nat :=
  Nat.land (nat_lit 1) (Nat.shiftRight (caMix32Raw x) (nat_lit 31))

theorem bit31_eq (x : Nat) :
    Nat.land (nat_lit 1) (Nat.shiftRight x (nat_lit 31)) = (if x.testBit 31 then 1 else 0) := by
  show (1 &&& (x >>> 31)) = if ((1 &&& (x >>> 31)) != 0) then 1 else 0
  have h : 1 &&& (x >>> 31) ≤ 1 := Nat.and_le_left
  generalize 1 &&& (x >>> 31) = b at h
  match b with
  | 0 => rfl
  | 1 => rfl
  | n + 2 => omega

theorem cellBitRaw_eq (x : Nat) : cellBitRaw x = (if (caMix32 x).testBit 31 then 1 else 0) := by
  unfold cellBitRaw
  rw [caMix32Raw_eq, bit31_eq]

noncomputable def cellRaw (seed i : Nat) : Nat :=
  @Bool.rec (fun _ => Nat)
    (@Bool.rec (fun _ => Nat)
      (cellBitRaw (Nat.add seed (Nat.mul (Nat.add i (nat_lit 1)) cK)))
      (nat_lit 0)
      (Nat.beq i (nat_lit 1)))
    (nat_lit 1)
    (Nat.beq i (nat_lit 0))

def cellBool (seed i : Nat) : Bool :=
  if i = 0 then true
  else if i = 1 then false
  else (caMix32 (seed + (i + 1) * 0x9e3779b9)).testBit 31

theorem beq_zero_true : ∀ {{x : Nat}}, Nat.beq x (nat_lit 0) = true → x = 0
  | 0, _ => rfl
  | _ + 1, h => Bool.noConfusion h

theorem beq_zero_false {{x : Nat}} (h : Nat.beq x (nat_lit 0) = false) : x ≠ 0 := by
  intro hx; subst hx; revert h; decide

theorem beq_one_true : ∀ {{x : Nat}}, Nat.beq x (nat_lit 1) = true → x = 1
  | 0, h => Bool.noConfusion h
  | 1, _ => rfl
  | _ + 2, h => Bool.noConfusion h

theorem beq_one_false {{x : Nat}} (h : Nat.beq x (nat_lit 1) = false) : x ≠ 1 := by
  intro hx; subst hx; revert h; decide

theorem cellRaw_eq (seed i : Nat) : cellRaw seed i = (if cellBool seed i then 1 else 0) := by
  unfold cellRaw cellBool
  cases h0 : Nat.beq i (nat_lit 0)
  · dsimp only
    have hi0 : i ≠ 0 := beq_zero_false h0
    rw [if_neg hi0]
    cases h1 : Nat.beq i (nat_lit 1)
    · dsimp only
      have hi1 : i ≠ 1 := beq_one_false h1
      rw [if_neg hi1, cellBitRaw_eq]
      simp only [hadd_eq, hmul_eq, cK_eq]
      rfl
    · dsimp only
      have hi1 : i = 1 := beq_one_true h1
      rw [if_pos hi1]
      rfl
  · dsimp only
    have hi0 : i = 0 := beq_zero_true h0
    rw [if_pos hi0]
    rfl

def stepAccRaw (b acc : Nat) : Nat := Nat.add (Nat.mul (nat_lit 2) acc) b

theorem stepAccRaw_eq (b acc : Nat) : stepAccRaw b acc = 2 * acc + b := by
  unfold stepAccRaw; simp only [hadd_eq, hmul_eq]

def initUnrolledG (stepF : Nat → Nat → Nat) (cellF : Nat → Nat) (z : Nat) : Nat :=
  {g_acc}

theorem initUnrolledG_eq (stepF : Nat → Nat → Nat) (cellF : Nat → Nat) (z : Nat) :
    initUnrolledG stepF cellF z = (List.range 256).foldr (fun i acc => stepF (cellF i) acc) z := rfl

def initBitsRaw (seed : Nat) : Nat :=
  {r_acc}

theorem initBitsRaw_eq_unrolled (seed : Nat) :
    initBitsRaw seed = initUnrolledG stepAccRaw (cellRaw seed) (nat_lit 0) := rfl

theorem foldr_cell_eq (seed : Nat) : ∀ (l : List Nat),
    l.foldr (fun i acc => stepAccRaw (cellRaw seed i) acc) (nat_lit 0) =
    encodeRow (l.map (cellBool seed))
  | [] => rfl
  | i :: is => by
      show stepAccRaw (cellRaw seed i) (is.foldr (fun i acc => stepAccRaw (cellRaw seed i) acc) (nat_lit 0)) =
           2 * encodeRow (is.map (cellBool seed)) + (if cellBool seed i then 1 else 0)
      rw [stepAccRaw_eq, cellRaw_eq, foldr_cell_eq seed is]

theorem initBitsRaw_eq_spec (seed : Nat) : initBitsRaw seed = encodeRow (initRowFor seed) := by
  rw [initBitsRaw_eq_unrolled, initUnrolledG_eq, foldr_cell_eq]
  rfl

/-! ### Bridge to the spec (identical to the official example) -/

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
    simp only [bstep, Nat.testBit_and, Nat.testBit_xor, Nat.testBit_or, testBit_M,
               testBit_rotL hm hi, testBit_rotR hm hi, testBit_encodeRow, hi, decide_true]
    generalize row.getD ((i + 255) % 256) false = a
    generalize row.getD i false = b
    generalize row.getD ((i + 1) % 256) false = c
    cases a <;> cases b <;> cases c <;> decide
  · rw [if_neg hi]
    unfold bstep
    rw [Nat.testBit_and, testBit_M, decide_eq_false hi, Bool.and_false]

theorem iter_eq : ∀ (n : Nat) (row : List Bool), row.length = 256 →
    encodeRow (iterRow n row) = biter n (encodeRow row) := by
  intro n
  induction n with
  | zero => intro row _; rfl
  | succ k ih =>
    intro row hlen
    show encodeRow (iterRow k (stepRow row)) = biter k (bstep (encodeRow row))
    rw [ih (stepRow row) (by rw [length_stepRow, hlen]), step_eq hlen]

noncomputable def impl : Nat → Nat := fun n =>
  biterRaw (caStepsRaw n) (initBitsRaw (caSeedRaw n))

theorem impl_correct : ∀ n, impl n = caSpecN n := by
  intro n
  show biterRaw (caStepsRaw n) (initBitsRaw (caSeedRaw n)) = caSpecN n
  rw [caStepsRaw_eq, caSeedRaw_eq, initBitsRaw_eq_spec, biterRaw_eq]
  show biter (caSteps n) (encodeRow (initRowFor (caSeed n))) =
    encodeRow (iterRow (caSteps n) (initRowFor (caSeed n)))
  rw [iter_eq (caSteps n) (initRowFor (caSeed n))
    (by simp [initRowFor, ruleWidth])]

end Submission
"""
    DST.write_text(src)
    print(f"wrote {DST} ({len(src)} bytes)")


if __name__ == "__main__":
    main()
