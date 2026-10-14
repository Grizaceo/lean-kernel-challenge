import Spec

/-!
# fib-v2 — Primitive Continuation-Passing Fast Doubling with Unrolled Prefix

Based on the F16 kernel cost model:
1. Eliminates all typeclass projections (`HAdd.hAdd`, `HMul.hMul`, `HSub.hSub`,
   `HDiv.hDiv`, `HMod.hMod`, `OfNat.ofNat`, `ite`, `Decidable`) from `impl` in
   favor of raw kernel primitives (`Nat.add`, `Nat.mul`, `Nat.sub`, `Nat.div`,
   `Nat.mod`, `Nat.beq`, `@Bool.rec`, `@Nat.rec`) and raw literals `(nat_lit k)`.
2. Uses Continuation-Passing Style (`(Nat → Nat → Nat) → Nat`) to eliminate
   `Prod` (`Nat × Nat`) allocations and projections at every doubling level.
3. Unrolls 18 levels of `step1` around `fdCps n`. Because `fdCps` is defined via
   `@Nat.rec` with step function `(fun _ ih => step1 ih)`, `step1 (fdCps fuel)`
   is definitionally equal (`rfl`) to `fdCps (fuel + 1)`. Thus the 18-level
   unrolled `impl n` is definitionally equal to `fdCps (n + 18) n (fun a _ => a)`,
   making the proof of `impl_correct` a one-line application of `fdCps_spec` while
   avoiding `@Nat.rec` unfolds during computation replay for all `n < 2^18`.
-/

namespace Submission

macro "unroll1% " ih:term : term =>
  `(fun (n : Nat) (k : Nat → Nat → Nat) =>
    @Bool.rec (fun _ => Nat)
      ($ih (Nat.div n (nat_lit 2)) (fun a b =>
        @Bool.rec (fun _ => Nat)
          (k (Nat.add (Nat.mul b b) (Nat.mul a a)) (Nat.mul b (Nat.add (Nat.add a a) b)))
          (k (Nat.mul a (Nat.sub (Nat.add b b) a)) (Nat.add (Nat.mul b b) (Nat.mul a a)))
          (Nat.beq (Nat.mod n (nat_lit 2)) (nat_lit 0))))
      (k (nat_lit 0) (nat_lit 1))
      (Nat.beq n (nat_lit 0)))

noncomputable def step1 (ih : Nat → (Nat → Nat → Nat) → Nat) (n : Nat) (k : Nat → Nat → Nat) : Nat :=
  (unroll1% ih) n k

noncomputable def fdCps : Nat → Nat → (Nat → Nat → Nat) → Nat :=
  @Nat.rec (fun _ => Nat → (Nat → Nat → Nat) → Nat)
    (fun _ k => k (nat_lit 0) (nat_lit 1))
    (fun _ ih => step1 ih)

noncomputable def impl (n : Nat) : Nat :=
  (unroll1% (unroll1% (unroll1% (unroll1% (unroll1% (unroll1% (unroll1% (unroll1% (unroll1% (unroll1% (unroll1% (unroll1% (unroll1% (unroll1% (unroll1% (unroll1% (unroll1% (unroll1% (fdCps n))))))))))))))))))) n (fun a _ => a)

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

theorem beq_zero_false {x : Nat} (h : Nat.beq x (nat_lit 0) = false) : x ≠ 0 := by
  intro hx; subst hx; revert h; decide

theorem beq_zero_true : ∀ {x : Nat}, Nat.beq x (nat_lit 0) = true → x = 0
  | 0, _ => rfl
  | _ + 1, h => Bool.noConfusion h

theorem step1_spec (ih : Nat → (Nat → Nat → Nat) → Nat) (n : Nat)
    (hih : ∀ m, m ≤ n / 2 → ∀ k : Nat → Nat → Nat, ih m k = k (Nat.fib m) (Nat.fib (m + 1)))
    (k : Nat → Nat → Nat) :
    step1 ih n k = k (Nat.fib n) (Nat.fib (n + 1)) := by
  unfold step1
  dsimp only
  cases h0 : Nat.beq n (nat_lit 0)
  · dsimp only
    have hn0 : n ≠ 0 := beq_zero_false h0
    have hdiv_eq : Nat.div n (nat_lit 2) = n / 2 := rfl
    rw [hdiv_eq, hih (n / 2) (Nat.le_refl _)]
    cases hpar : Nat.beq (Nat.mod n (nat_lit 2)) (nat_lit 0)
    · dsimp only
      have hmod0 : n % 2 ≠ 0 := beq_zero_false hpar
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
      have hmod : n % 2 = 0 := beq_zero_true hpar
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
    have hn0 : n = 0 := beq_zero_true h0
    subst hn0
    rfl

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
  exact fdCps_spec (n + 18) n (by omega) (fun a _ => a)

end Submission
