#!/usr/bin/env python3
"""Generate candidates/fib-v3/Submission.lean."""
import sys
from pathlib import Path

sys.set_int_max_str_digits(500_000)

ROOT = Path("/home/gris96/.hermes/workspace/repos/SAIR/lean-kernel-challenge")
CAND_DIR = ROOT / "candidates" / "fib-v3"
CAND_DIR.mkdir(parents=True, exist_ok=True)
DST = CAND_DIR / "Submission.lean"

MAX_BASE = 511
LANE_BITS = 512
SHIFT_LOG2 = 9
UNROLL_LEVELS = 9
M512 = (1 << LANE_BITS) - 1

fibs = [0, 1]
for i in range(2, MAX_BASE + 3):
    fibs.append(fibs[-1] + fibs[-2])

tbl = 0
for k in range(MAX_BASE + 2):
    assert fibs[k] <= M512
    tbl |= (fibs[k] << (LANE_BITS * k))

unroll_expr = "(fdCps n)"
for _ in range(UNROLL_LEVELS):
    unroll_expr = f"(unroll1% {unroll_expr})"

src = f"""import Spec

namespace Submission

set_option maxRecDepth 100000
set_option exponentiation.threshold 2048

/-!
# fib-v3 — Primitive CPS Fast Doubling + Outer `Bool.rec` + 512-Entry Packed Base Table

Improvements over `fib-v2`:
1. Moves `@Bool.rec` on the parity bit `n & 1 == 0` outside the continuation
   lambda `fun a b => ...`, so `whnf` discards the untaken parity branch before
   `instantiate_rev` substitutes `a` and `b`.
2. Replaces `Nat.div n 2` and `Nat.mod n 2` with `Nat.shiftRight n 1` and
   `Nat.land n 1`.
3. Stops the doubling recursion at `n ≤ 511` (`Nat.ble n 511`), extracting both
   `F(n)` and `F(n + 1)` from a single 513-entry packed 512-bit-lane constant
   table (`fibTableLit = tableGo 511`), skipping the bottom 9 doubling levels on
   every input and reducing the unrolled depth from 18 to 9.
-/

def fibTableLit : Nat := (nat_lit {tbl})
def m512Lit : Nat := (nat_lit {M512})

def baseFib (n : Nat) (k : Nat → Nat → Nat) : Nat :=
  let w := Nat.shiftRight (nat_lit {tbl}) (Nat.shiftLeft n (nat_lit {SHIFT_LOG2}))
  k (Nat.land w (nat_lit {M512})) (Nat.land (Nat.shiftRight w (nat_lit {LANE_BITS})) (nat_lit {M512}))

macro "unroll1% " ih:term : term =>
  `(fun (n : Nat) (k : Nat → Nat → Nat) =>
    @Bool.rec (fun _ => Nat)
      ($ih (Nat.shiftRight n (nat_lit 1))
        (@Bool.rec (fun _ => Nat → Nat → Nat)
          (fun a b => k (Nat.add (Nat.mul b b) (Nat.mul a a)) (Nat.mul b (Nat.add (Nat.add a a) b)))
          (fun a b => k (Nat.mul a (Nat.sub (Nat.add b b) a)) (Nat.add (Nat.mul b b) (Nat.mul a a)))
          (Nat.beq (Nat.land n (nat_lit 1)) (nat_lit 0))))
      (baseFib n k)
      (Nat.ble n (nat_lit {MAX_BASE})))

noncomputable def step1 (ih : Nat → (Nat → Nat → Nat) → Nat) (n : Nat) (k : Nat → Nat → Nat) : Nat :=
  (unroll1% ih) n k

noncomputable def fdCps : Nat → Nat → (Nat → Nat → Nat) → Nat :=
  @Nat.rec (fun _ => Nat → (Nat → Nat → Nat) → Nat)
    (fun _ k => k (nat_lit 0) (nat_lit 1))
    (fun _ ih => step1 ih)

noncomputable def impl (n : Nat) : Nat :=
  {unroll_expr} n (fun a _ => a)

/-! ### Part 1: Fast-doubling identities -/

theorem fib_odd (m : Nat) :
    Nat.fib (2 * m + 1) = Nat.fib (m + 1) * Nat.fib (m + 1) + Nat.fib m * Nat.fib m := by
  simpa only [pow_two] using Nat.fib_two_mul_add_one m

theorem fib_even (m : Nat) :
    Nat.fib (2 * m) = Nat.fib m * (2 * Nat.fib (m + 1) - Nat.fib m) :=
  Nat.fib_two_mul m

theorem two_mul_eq_add (x : Nat) : 2 * x = x + x := by omega

theorem fib_even_step (m : Nat) :
    Nat.fib (2 * m) = Nat.fib m * ((Nat.fib (m + 1) + Nat.fib (m + 1)) - Nat.fib m) := by
  rw [fib_even, two_mul_eq_add]

theorem fib_odd_next (m : Nat) :
    Nat.fib (2 * m + 2) = Nat.fib (m + 1) * ((Nat.fib m + Nat.fib m) + Nat.fib (m + 1)) := by
  have hsum : Nat.fib (2 * m + 2) = Nat.fib (2 * m) + Nat.fib (2 * m + 1) := Nat.fib_add_two
  rw [hsum, fib_even_step, fib_odd]
  have hfib_le : Nat.fib m ≤ Nat.fib (m + 1) := Nat.fib_le_fib_succ
  generalize Nat.fib m = a at *
  generalize Nat.fib (m + 1) = b at *
  have hle : a ≤ b + b := by omega
  have hmul_le : a * a ≤ a * (b + b) := Nat.mul_le_mul_left a hle
  rw [Nat.mul_sub_left_distrib]
  have hab : a * (b + b) = a * b + a * b := Nat.mul_add a b b
  have hba : b * ((a + a) + b) = b * a + b * a + b * b := by
    rw [Nat.mul_add, Nat.mul_add]
  have hcomm : b * a = a * b := Nat.mul_comm b a
  omega

theorem fib_lt_two_pow : ∀ k : Nat, Nat.fib k < 2 ^ k
  | 0 => by decide
  | 1 => by decide
  | k + 2 => by
    rw [Nat.fib_add_two, Nat.pow_succ, Nat.pow_succ]
    have h0 := fib_lt_two_pow k
    have h1 := fib_lt_two_pow (k + 1)
    rw [Nat.pow_succ] at h1
    omega

/-! ### Part 2: 512-bit-lane base table (`tableGo 511`) -/

noncomputable def tableGo : Nat → Nat :=
  @Nat.rec (fun _ => Nat)
    (Nat.shiftLeft (nat_lit 1) (nat_lit 512))
    (fun m tbl =>
      let m1 := Nat.add m (nat_lit 1)
      let m2 := Nat.add m (nat_lit 2)
      let fm := Nat.land (Nat.shiftRight tbl (Nat.shiftLeft m (nat_lit 9))) m512Lit
      let fm1 := Nat.land (Nat.shiftRight tbl (Nat.shiftLeft m1 (nat_lit 9))) m512Lit
      let fm2 := Nat.land (Nat.add fm fm1) m512Lit
      Nat.lor tbl (Nat.shiftLeft fm2 (Nat.shiftLeft m2 (nat_lit 9))))

theorem fibTableLit_eq : fibTableLit = tableGo (nat_lit {MAX_BASE}) := rfl

theorem testBit_high {{m W : Nat}} (hm : m < 2 ^ W) {{j : Nat}} (hj : W ≤ j) : m.testBit j = false := by
  have hlt : m < 2 ^ j := Nat.lt_of_lt_of_le hm (Nat.pow_le_pow_right (by omega) hj)
  simp [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hlt]

theorem m512_eq : m512Lit = 2 ^ 512 - 1 := by decide

theorem and_m512_eq_mod (x : Nat) : (x &&& m512Lit) = x % 2 ^ 512 := by
  rw [m512_eq]
  exact Nat.and_two_pow_sub_one_eq_mod x 512

theorem and_m512_lt (x : Nat) : (x &&& m512Lit) < 2 ^ 512 := by
  rw [and_m512_eq_mod]
  exact Nat.mod_lt x (by decide)

theorem testBit_m512 (j : Nat) : m512Lit.testBit j = decide (j < 512) := by
  rw [m512_eq]
  exact Nat.testBit_two_pow_sub_one 512 j

theorem shl9_eq (k : Nat) : (k <<< 9) = 512 * k := by
  rw [Nat.shiftLeft_eq]; omega

theorem tableGo_lt : ∀ m, tableGo m < 2 ^ (512 * (m + 2))
  | 0 => by
    show (1 <<< 512) < 2 ^ (512 * 2)
    decide
  | m + 1 => by
    show (let m1 := m + 1
          let m2 := m + 2
          let fm := (tableGo m >>> (m <<< 9)) &&& m512Lit
          let fm1 := (tableGo m >>> (m1 <<< 9)) &&& m512Lit
          let fm2 := (fm + fm1) &&& m512Lit
          tableGo m ||| (fm2 <<< (m2 <<< 9))) < 2 ^ (512 * (m + 3))
    dsimp only
    apply Nat.or_lt_two_pow
    · exact Nat.lt_of_lt_of_le (tableGo_lt m) (Nat.pow_le_pow_right (by omega) (by omega))
    · rw [shl9_eq (m + 2), Nat.shiftLeft_eq]
      have hlt := and_m512_lt (((tableGo m >>> (m <<< 9)) &&& m512Lit) +
                  ((tableGo m >>> ((m + 1) <<< 9)) &&& m512Lit))
      generalize (((tableGo m >>> (m <<< 9)) &&& m512Lit) +
                  ((tableGo m >>> ((m + 1) <<< 9)) &&& m512Lit)) &&& m512Lit = fm2 at hlt ⊢
      have h1 : fm2 * 2 ^ (512 * (m + 2)) ≤ (2 ^ 512 - 1) * 2 ^ (512 * (m + 2)) :=
        Nat.mul_le_mul_right _ (by omega)
      rw [Nat.sub_mul, Nat.one_mul, ← Nat.pow_add] at h1
      have h2 : 512 + 512 * (m + 2) = 512 * (m + 3) := by omega
      rw [h2] at h1
      have hpos : 1 ≤ 2 ^ (512 * (m + 2)) := Nat.one_le_two_pow
      have hpos2 : 2 ^ (512 * (m + 2)) ≤ 2 ^ (512 * (m + 3)) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      omega

def extract512 (tbl k : Nat) : Nat := (tbl >>> (k <<< 9)) &&& m512Lit

theorem tableGo_extract : ∀ m k, k ≤ m + 1 → extract512 (tableGo m) k = (Nat.fib k &&& m512Lit)
  | 0, k, hk => by
    rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
    · decide
    · decide
  | m + 1, k, hk => by
    have hstep : tableGo (m + 1) =
        (tableGo m ||| ((((extract512 (tableGo m) m) + (extract512 (tableGo m) (m + 1))) &&& m512Lit) <<< ((m + 2) <<< 9))) := rfl
    by_cases hkm : k ≤ m + 1
    · rw [hstep]
      have ih := tableGo_extract m k hkm
      rw [← ih]
      unfold extract512
      apply Nat.eq_of_testBit_eq; intro j
      rw [Nat.testBit_and, Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_shiftRight,
          Nat.testBit_or, Nat.testBit_shiftLeft]
      simp only [testBit_m512]
      by_cases hj : j < 512
      · simp only [hj, decide_true, Bool.and_true]
        have hnot : ¬ ((m + 2) <<< 9 ≤ (k <<< 9) + j) := by
          rw [shl9_eq, shl9_eq]; omega
        simp [hnot]
      · simp [hj]
    · have hk_eq : k = m + 2 := by omega
      subst hk_eq
      rw [hstep, tableGo_extract m m (by omega), tableGo_extract m (m + 1) (by omega)]
      have hmod : (((Nat.fib m &&& m512Lit) + (Nat.fib (m + 1) &&& m512Lit)) &&& m512Lit) =
          (Nat.fib (m + 2) &&& m512Lit) := by
        rw [Nat.fib_add_two, and_m512_eq_mod, and_m512_eq_mod, and_m512_eq_mod,
            and_m512_eq_mod (Nat.fib m + Nat.fib (m + 1)), Nat.add_mod_mod, Nat.mod_add_mod]
      rw [hmod]
      unfold extract512
      apply Nat.eq_of_testBit_eq; intro j
      simp only [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_or, Nat.testBit_shiftLeft, testBit_m512]
      by_cases hj : j < 512
      · simp only [hj, decide_true, Bool.and_true]
        have hlo : (tableGo m).testBit (((m + 2) <<< 9) + j) = false := by
          apply testBit_high (tableGo_lt m)
          rw [shl9_eq]; omega
        have hge : ((m + 2) <<< 9) ≤ ((m + 2) <<< 9) + j := by omega
        have hsub : ((m + 2) <<< 9) + j - ((m + 2) <<< 9) = j := by omega
        simp [hlo, hge, hsub, hj]
      · simp [hj]

theorem baseFib_spec {{n : Nat}} (hn : n ≤ {MAX_BASE}) (k : Nat → Nat → Nat) :
    baseFib n k = k (Nat.fib n) (Nat.fib (n + 1)) := by
  unfold baseFib
  dsimp only
  have h1 : Nat.land (Nat.shiftRight (nat_lit {tbl}) (Nat.shiftLeft n (nat_lit 9))) (nat_lit {M512}) =
      extract512 fibTableLit n := rfl
  have h2 : Nat.land (Nat.shiftRight (Nat.shiftRight (nat_lit {tbl}) (Nat.shiftLeft n (nat_lit 9))) (nat_lit 512)) (nat_lit {M512}) =
      extract512 fibTableLit (n + 1) := by
    change ((fibTableLit >>> (n <<< 9)) >>> 512) &&& m512Lit = (fibTableLit >>> ((n + 1) <<< 9)) &&& m512Lit
    rw [← Nat.shiftRight_add, shl9_eq n, shl9_eq (n + 1)]
    have heq : 512 * n + 512 = 512 * (n + 1) := by omega
    rw [heq]
  rw [h1, h2, fibTableLit_eq,
      tableGo_extract {MAX_BASE} n (by omega),
      tableGo_extract {MAX_BASE} (n + 1) (by omega),
      and_m512_eq_mod, and_m512_eq_mod]
  have hlt1 : Nat.fib n < 2 ^ 512 :=
    Nat.lt_of_lt_of_le (fib_lt_two_pow n) (Nat.pow_le_pow_right (by omega) (by omega))
  have hlt2 : Nat.fib (n + 1) < 2 ^ 512 :=
    Nat.lt_of_lt_of_le (fib_lt_two_pow (n + 1)) (Nat.pow_le_pow_right (by omega) (by omega))
  rw [Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt hlt2]

/-! ### Part 3: Correctness of `step1`, `fdCps`, and `impl` -/

theorem beq_zero_false {{x : Nat}} (h : Nat.beq x (nat_lit 0) = false) : x ≠ 0 := by
  intro hx; subst hx; revert h; decide

theorem beq_zero_true : ∀ {{x : Nat}}, Nat.beq x (nat_lit 0) = true → x = 0
  | 0, _ => rfl
  | _ + 1, h => Bool.noConfusion h

theorem ble_false_gt {{a b : Nat}} (h : Nat.ble a b = false) : b < a :=
  Nat.gt_of_not_le (mt Nat.ble_eq_true_of_le (by simp [h]))

theorem shr1_eq_div2 (n : Nat) : Nat.shiftRight n (nat_lit 1) = n / 2 := by
  change n >>> 1 = n / 2
  rw [Nat.shiftRight_eq_div_pow]

theorem land1_eq_mod2 (n : Nat) : Nat.land n (nat_lit 1) = n % 2 := by
  change n &&& (2 ^ 1 - 1) = n % 2 ^ 1
  exact Nat.and_two_pow_sub_one_eq_mod n 1

theorem step1_spec (ih : Nat → (Nat → Nat → Nat) → Nat) (n : Nat)
    (hih : ∀ m, m ≤ n / 2 → ∀ k : Nat → Nat → Nat, ih m k = k (Nat.fib m) (Nat.fib (m + 1)))
    (k : Nat → Nat → Nat) :
    step1 ih n k = k (Nat.fib n) (Nat.fib (n + 1)) := by
  unfold step1
  dsimp only
  cases hle : Nat.ble n (nat_lit {MAX_BASE})
  · dsimp only
    rw [shr1_eq_div2, hih (n / 2) (Nat.le_refl _)]
    cases hpar : Nat.beq (Nat.land n (nat_lit 1)) (nat_lit 0)
    · dsimp only
      have hmod0 : n % 2 ≠ 0 := by
        rw [← land1_eq_mod2]
        exact beq_zero_false hpar
      have hmod : n % 2 = 1 := by omega
      have e1 : 2 * (n / 2) + 1 = n := by omega
      have e2 : 2 * (n / 2) + 2 = n + 1 := by omega
      have ho := (fib_odd (n / 2)).symm
      have hn := (fib_odd_next (n / 2)).symm
      rw [e1] at ho
      rw [e2] at hn
      change k (Nat.fib (n / 2 + 1) * Nat.fib (n / 2 + 1) + Nat.fib (n / 2) * Nat.fib (n / 2))
               (Nat.fib (n / 2 + 1) * ((Nat.fib (n / 2) + Nat.fib (n / 2)) + Nat.fib (n / 2 + 1)))
             = k (Nat.fib n) (Nat.fib (n + 1))
      rw [ho, hn]
    · dsimp only
      have hmod : n % 2 = 0 := by
        rw [← land1_eq_mod2]
        exact beq_zero_true hpar
      have e1 : 2 * (n / 2) = n := by omega
      have e2 : 2 * (n / 2) + 1 = n + 1 := by omega
      have he := (fib_even_step (n / 2)).symm
      have ho := (fib_odd (n / 2)).symm
      rw [e1] at he
      rw [e2] at ho
      change k (Nat.fib (n / 2) * ((Nat.fib (n / 2 + 1) + Nat.fib (n / 2 + 1)) - Nat.fib (n / 2)))
               (Nat.fib (n / 2 + 1) * Nat.fib (n / 2 + 1) + Nat.fib (n / 2) * Nat.fib (n / 2))
             = k (Nat.fib n) (Nat.fib (n + 1))
      rw [he, ho]
  · dsimp only
    exact baseFib_spec (Nat.le_of_ble_eq_true hle) k

theorem fdCps_spec : ∀ (fuel n : Nat), n ≤ fuel → ∀ (k : Nat → Nat → Nat),
    fdCps fuel n k = k (Nat.fib n) (Nat.fib (n + 1))
  | 0, n, h, k => by
    have hn0 : n = 0 := by omega
    subst hn0
    rfl
  | fuel + 1, n, h, k => by
    change step1 (fdCps fuel) n k = k (Nat.fib n) (Nat.fib (n + 1))
    apply step1_spec
    intro m hm k'
    exact fdCps_spec fuel m (by omega) k'

theorem impl_correct : ∀ n, impl n = Nat.fib n := by
  intro n
  exact fdCps_spec (n + {UNROLL_LEVELS}) n (by omega) (fun a _ => a)

end Submission
"""

DST.write_text(src)
print(f"wrote {DST} ({len(src)} bytes)")
