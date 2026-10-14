#!/usr/bin/env python3
"""Generate candidates/polydisc-v2/Submission.lean."""
from pathlib import Path

ROOT = Path("/home/gris96/.hermes/workspace/repos/SAIR/lean-kernel-challenge")
CAND_DIR = ROOT / "candidates" / "polydisc-v2"
CAND_DIR.mkdir(parents=True, exist_ok=True)
DST = CAND_DIR / "Submission.lean"

src = """import Spec

namespace Submission

/-!
# polydisc-v2 — Raw-Primitive Subresultant PRS & Polynomial Generator (F16 Rule)

Eliminates all `Int` and `Nat` typeclass projections (`@HAdd.hAdd`, `@HSub.hSub`,
`@HMul.hMul`, `@HDiv.hDiv`, `@HMod.hMod`, `@HPow.hPow`, `@OfNat.ofNat`, `@ite`,
`Decidable`, `BEq`, and equation-compiler `brecOn`) from both `polyOf` and the
subresultant PRS hot path of `discSpec`, replacing them with direct `@Int.casesOn`,
`@Nat.rec`, `@List.rec`, `@Bool.rec`, and raw kernel primitives (`Nat.add`,
`Nat.sub`, `Nat.mul`, `Nat.div`, `Nat.mod`, `Nat.shiftLeft`, `Nat.shiftRight`,
`Nat.beq`, `Nat.ble`) with `(nat_lit k)` literals.
-/

/-! ### Part 1: Raw `Nat` and `Bool` helper lemmas -/

theorem ble_eq_decide (a b : Nat) : Nat.ble a b = decide (a ≤ b) := by
  cases h : Nat.ble a b
  · exact (decide_eq_false (Nat.not_le.mpr (Nat.gt_of_not_le (mt Nat.ble_eq_true_of_le (by simp [h]))))).symm
  · exact (decide_eq_true (Nat.le_of_ble_eq_true h)).symm

theorem blt_eq_decide (a b : Nat) : Nat.ble (Nat.add a (nat_lit 1)) b = decide (a < b) := by
  change Nat.ble (a + 1) b = decide (a < b)
  rw [ble_eq_decide]
  by_cases h : a < b
  · have hle : a + 1 ≤ b := h
    simp [h, hle]
  · have hle : ¬ (a + 1 ≤ b) := h
    simp [h, hle]

theorem beq_eq_beq (a b : Nat) : Nat.beq a b = (a == b) := by
  cases h1 : Nat.beq a b
  · have hne : a ≠ b := by intro heq; subst heq; rw [Nat.beq_refl] at h1; contradiction
    exact (beq_false_of_ne hne).symm
  · have heq : a = b := Nat.eq_of_beq_eq_true h1
    subst heq; simp

/-! ### Part 2: Raw `Int` arithmetic primitives -/

noncomputable def negOfNatR (n : Nat) : Int :=
  @Bool.rec (fun _ => Int)
    (Int.negSucc (Nat.sub n (nat_lit 1)))
    (Int.ofNat (nat_lit 0))
    (Nat.beq n (nat_lit 0))

theorem negOfNatR_eq (n : Nat) : negOfNatR n = Int.negOfNat n := by
  unfold negOfNatR Int.negOfNat
  change @Bool.rec (fun _ => Int) (Int.negSucc (n - 1)) (Int.ofNat 0) (Nat.beq n 0) = _
  cases n <;> rfl

noncomputable def subNatR (m n : Nat) : Int :=
  let d := Nat.sub n m
  @Bool.rec (fun _ => Int)
    (Int.negSucc (Nat.sub d (nat_lit 1)))
    (Int.ofNat (Nat.sub m n))
    (Nat.beq d (nat_lit 0))

theorem subNatR_eq (m n : Nat) : subNatR m n = Int.subNatNat m n := by
  unfold subNatR Int.subNatNat
  dsimp only
  change @Bool.rec (fun _ => Int) (Int.negSucc ((n - m) - 1)) (Int.ofNat (m - n)) (Nat.beq (n - m) 0) = _
  cases (n - m) <;> rfl

theorem ofNat_sub_ofNat_eq (m n : Nat) : (Int.ofNat m - Int.ofNat n) = Int.subNatNat m n :=
  Int.subNatNat_eq_coe.symm

noncomputable def intNegR (a : Int) : Int :=
  @Int.casesOn (fun _ => Int) a
    (fun m => negOfNatR m)
    (fun m => Int.ofNat (Nat.add m (nat_lit 1)))

theorem intNegR_eq (a : Int) : intNegR a = -a := by
  cases a with
  | ofNat m => exact negOfNatR_eq m
  | negSucc m => rfl

noncomputable def intAddR (a b : Int) : Int :=
  @Int.casesOn (fun _ => Int) a
    (fun m => @Int.casesOn (fun _ => Int) b
      (fun n => Int.ofNat (Nat.add m n))
      (fun n => subNatR m (Nat.add n (nat_lit 1))))
    (fun m => @Int.casesOn (fun _ => Int) b
      (fun n => subNatR n (Nat.add m (nat_lit 1)))
      (fun n => Int.negSucc (Nat.add (Nat.add m n) (nat_lit 1))))

theorem intAddR_eq (a b : Int) : intAddR a b = a + b := by
  cases a <;> cases b
  · rfl
  · exact subNatR_eq _ _
  · exact subNatR_eq _ _
  · rfl

noncomputable def intSubR (a b : Int) : Int :=
  @Int.casesOn (fun _ => Int) a
    (fun m => @Int.casesOn (fun _ => Int) b
      (fun n => subNatR m n)
      (fun n => Int.ofNat (Nat.add m (Nat.add n (nat_lit 1)))))
    (fun m => @Int.casesOn (fun _ => Int) b
      (fun n => Int.negSucc (Nat.add m n))
      (fun n => subNatR n m))

theorem subNatNat_succ_succ (n m : Nat) :
    Int.subNatNat (n + 1) (m + 1) = Int.subNatNat n m := by
  unfold Int.subNatNat
  have h1 : (m + 1) - (n + 1) = m - n := Nat.add_sub_add_right m 1 n
  have h2 : (n + 1) - (m + 1) = n - m := Nat.add_sub_add_right n 1 m
  rw [h1, h2]

theorem intSubR_eq (a b : Int) : intSubR a b = a - b := by
  cases a with
  | ofNat m =>
    cases b with
    | ofNat n =>
      show subNatR m n = Int.ofNat m - Int.ofNat n
      rw [subNatR_eq, ofNat_sub_ofNat_eq]
    | negSucc n => rfl
  | negSucc m =>
    cases b with
    | ofNat n =>
      cases n with
      | zero =>
        show Int.negSucc (m + 0) = Int.negSucc m
        rfl
      | succ k => rfl
    | negSucc n =>
      show subNatR n m = Int.subNatNat (n + 1) (m + 1)
      rw [subNatR_eq, subNatNat_succ_succ]

noncomputable def intMulR (a b : Int) : Int :=
  @Int.casesOn (fun _ => Int) a
    (fun m => @Int.casesOn (fun _ => Int) b
      (fun n => Int.ofNat (Nat.mul m n))
      (fun n => negOfNatR (Nat.mul m (Nat.add n (nat_lit 1)))))
    (fun m => @Int.casesOn (fun _ => Int) b
      (fun n => negOfNatR (Nat.mul (Nat.add m (nat_lit 1)) n))
      (fun n => Int.ofNat (Nat.mul (Nat.add m (nat_lit 1)) (Nat.add n (nat_lit 1)))))

theorem intMulR_eq (a b : Int) : intMulR a b = a * b := by
  cases a <;> cases b
  · rfl
  · exact negOfNatR_eq _
  · exact negOfNatR_eq _
  · rfl

noncomputable def intSqR (a : Int) : Int :=
  @Int.casesOn (fun _ => Int) a
    (fun m => Int.ofNat (Nat.mul m m))
    (fun m =>
      let m1 := Nat.add m (nat_lit 1)
      Int.ofNat (Nat.mul m1 m1))

theorem intSqR_eq (a : Int) : intSqR a = a ^ 2 := by
  rw [Int.pow_succ, Int.pow_succ, Int.pow_zero, Int.one_mul, ← intMulR_eq]
  cases a <;> rfl

noncomputable def intEdivR (x y : Int) : Int :=
  @Int.casesOn (fun _ => Int) x
    (fun m => @Int.casesOn (fun _ => Int) y
      (fun n => Int.ofNat (Nat.div m n))
      (fun n => negOfNatR (Nat.div m (Nat.add n (nat_lit 1)))))
    (fun m => @Int.casesOn (fun _ => Int) y
      (fun n => @Bool.rec (fun _ => Int)
        (Int.negSucc (Nat.div m n))
        (Int.ofNat (nat_lit 0))
        (Nat.beq n (nat_lit 0)))
      (fun n => Int.ofNat (Nat.add (Nat.div m (Nat.add n (nat_lit 1))) (nat_lit 1))))

theorem intEdivR_eq (x y : Int) : intEdivR x y = x / y := by
  cases x with
  | ofNat m =>
    cases y with
    | ofNat n => rfl
    | negSucc n => exact negOfNatR_eq _
  | negSucc m =>
    cases y with
    | ofNat n =>
      show @Bool.rec (fun _ => Int) (Int.negSucc (m / n)) (Int.ofNat 0) (Nat.beq n 0) = _
      cases n <;> rfl
    | negSucc n => rfl

noncomputable def natAbsR (y : Int) : Nat :=
  @Int.casesOn (fun _ => Nat) y
    (fun n => n)
    (fun n => Nat.add n (nat_lit 1))

theorem natAbsR_eq (y : Int) : natAbsR y = y.natAbs := by
  cases y <;> rfl

noncomputable def intEmodR (x y : Int) : Int :=
  let d := natAbsR y
  @Int.casesOn (fun _ => Int) x
    (fun m => Int.ofNat (Nat.mod m d))
    (fun m => subNatR d (Nat.add (Nat.mod m d) (nat_lit 1)))

theorem intEmodR_eq (x y : Int) : intEmodR x y = x % y := by
  unfold intEmodR
  dsimp only
  rw [natAbsR_eq]
  cases x with
  | ofNat m => rfl
  | negSucc m => exact subNatR_eq _ _

noncomputable def intBeqZeroR (x : Int) : Bool :=
  @Int.casesOn (fun _ => Bool) x
    (fun m => Nat.beq m (nat_lit 0))
    (fun _ => false)

theorem intBeqZeroR_eq (x : Int) : intBeqZeroR x = (x == 0) := by
  cases x with
  | ofNat m => cases m <;> rfl
  | negSucc m => rfl

noncomputable def intPowR (b : Int) : Nat → Int :=
  @Nat.rec (fun _ => Int)
    (Int.ofNat (nat_lit 1))
    (fun _ acc => intMulR acc b)

theorem intPowR_eq (b : Int) : ∀ e : Nat, intPowR b e = b ^ e
  | 0 => by rw [Int.pow_zero]; rfl
  | e + 1 => by
    show intMulR (intPowR b e) b = b ^ (e + 1)
    rw [intMulR_eq, intPowR_eq b e, Int.pow_succ]

/-! ### Part 3: Raw polynomial operations (`trimLeadingR`, `scalePolynomialR`, `cancelPseudoLeadingR`, `pseudoRemainderR`, `exactDividePolynomialR`, `normalResultantR`) -/

noncomputable def trimLeadingR : List Int → List Int :=
  @List.rec Int (fun _ => List Int)
    []
    (fun c cs ih =>
      @Bool.rec (fun _ => List Int)
        (c :: cs)
        ih
        (intBeqZeroR c))

theorem trimLeadingR_eq : ∀ l : List Int, trimLeadingR l = trimLeading l
  | [] => rfl
  | c :: cs => by
    show @Bool.rec (fun _ => List Int) (c :: cs) (trimLeadingR cs) (intBeqZeroR c) = trimLeading (c :: cs)
    rw [trimLeadingR_eq cs]
    cases c with
    | ofNat m =>
      cases m with
      | zero => rfl
      | succ k => rfl
    | negSucc m => rfl

noncomputable def scalePolynomialR (factor : Int) : List Int → List Int :=
  @List.rec Int (fun _ => List Int)
    []
    (fun c _ ih => intMulR factor c :: ih)

theorem scalePolynomialR_eq (factor : Int) : ∀ l : List Int,
    scalePolynomialR factor l = scalePolynomial factor l
  | [] => rfl
  | c :: cs => by
    show intMulR factor c :: scalePolynomialR factor cs = factor * c :: scalePolynomial factor cs
    rw [intMulR_eq, scalePolynomialR_eq factor cs]

theorem scalePolynomial_one : ∀ l : List Int, scalePolynomial (Int.ofNat 1) l = l
  | [] => rfl
  | c :: cs => by
    show (1 : Int) * c :: scalePolynomial (Int.ofNat 1) cs = c :: cs
    rw [Int.one_mul, scalePolynomial_one cs]

noncomputable def cancelPseudoLeadingR (lcG lcR : Int) : List Int → List Int → List Int :=
  @List.rec Int (fun _ => List Int → List Int)
    (fun _ => [])
    (fun c _ ih divs =>
      @List.casesOn Int (fun _ => List Int) divs
        (intMulR lcG c :: ih [])
        (fun d ds => intSubR (intMulR lcG c) (intMulR lcR d) :: ih ds))

theorem cancelPseudoLeadingR_eq (lcG lcR : Int) : ∀ (cs ds : List Int),
    cancelPseudoLeadingR lcG lcR cs ds = cancelPseudoLeading lcG lcR cs ds
  | [], _ => rfl
  | c :: cs, [] => by
    show intMulR lcG c :: cancelPseudoLeadingR lcG lcR cs [] =
      lcG * c :: cancelPseudoLeading lcG lcR cs []
    rw [intMulR_eq, cancelPseudoLeadingR_eq lcG lcR cs []]
  | c :: cs, d :: ds => by
    show intSubR (intMulR lcG c) (intMulR lcR d) :: cancelPseudoLeadingR lcG lcR cs ds =
      (lcG * c - lcR * d) :: cancelPseudoLeading lcG lcR cs ds
    rw [intSubR_eq, intMulR_eq, intMulR_eq, cancelPseudoLeadingR_eq lcG lcR cs ds]

noncomputable def listLenR : List Int → Nat :=
  @List.rec Int (fun _ => Nat)
    (nat_lit 0)
    (fun _ _ ih => Nat.add ih (nat_lit 1))

theorem listLenR_eq : ∀ l : List Int, listLenR l = l.length
  | [] => rfl
  | _ :: xs => by
    show listLenR xs + 1 = xs.length + 1
    rw [listLenR_eq xs]

noncomputable def headDR (d : Int) (l : List Int) : Int :=
  @List.casesOn Int (fun _ => Int) l d (fun h _ => h)

theorem headDR_eq (d : Int) (l : List Int) : headDR d l = l.headD d := by
  cases l <;> rfl

noncomputable def pseudoRemainderGoR :
    Nat → Nat → List Int → List Int → Option (List Int) :=
  @Nat.rec (fun _ => Nat → List Int → List Int → Option (List Int))
    (fun _ _ _ => none)
    (fun _ ih remaining divisor dividend =>
      let dividend := trimLeadingR dividend
      @Bool.rec (fun _ => Option (List Int))
        (@List.casesOn Int (fun _ => Option (List Int)) divisor
          none
          (fun lcG divisorTail =>
            @List.casesOn Int (fun _ => Option (List Int)) dividend
              none
              (fun lcR dividendTail =>
                let next := trimLeadingR (cancelPseudoLeadingR lcG lcR dividendTail divisorTail)
                ih (Nat.sub remaining (nat_lit 1)) divisor next)))
        (@Bool.rec (fun _ => Option (List Int))
          (some (scalePolynomialR (intPowR (headDR (Int.ofNat (nat_lit 0)) divisor) remaining) dividend))
          (some dividend)
          (Nat.beq remaining (nat_lit 0)))
        (Nat.ble (Nat.add (listLenR dividend) (nat_lit 1)) (listLenR divisor)))

theorem pseudoRemainderGoR_eq : ∀ (fuel remaining : Nat) (divisor dividend : List Int),
    pseudoRemainderGoR fuel remaining divisor dividend =
      pseudoRemainderGo fuel remaining divisor dividend
  | 0, _, _, _ => rfl
  | fuel + 1, remaining, divisor, dividend => by
    show (let dividend := trimLeadingR dividend
          @Bool.rec (fun _ => Option (List Int))
            (@List.casesOn Int (fun _ => Option (List Int)) divisor
              none
              (fun lcG divisorTail =>
                @List.casesOn Int (fun _ => Option (List Int)) dividend
                  none
                  (fun lcR dividendTail =>
                    let next := trimLeadingR (cancelPseudoLeadingR lcG lcR dividendTail divisorTail)
                    pseudoRemainderGoR fuel (Nat.sub remaining (nat_lit 1)) divisor next)))
            (@Bool.rec (fun _ => Option (List Int))
              (some (scalePolynomialR (intPowR (headDR (Int.ofNat (nat_lit 0)) divisor) remaining) dividend))
              (some dividend)
              (Nat.beq remaining (nat_lit 0)))
            (Nat.ble (Nat.add (listLenR dividend) (nat_lit 1)) (listLenR divisor))) =
          (let dividend := trimLeading dividend
           if dividend.length < divisor.length then
             some (scalePolynomial ((divisor.headD 0) ^ remaining) dividend)
           else
             match divisor, dividend with
             | lcG :: divisorTail, lcR :: dividendTail =>
                 let next :=
                   trimLeading
                     (cancelPseudoLeading lcG lcR dividendTail divisorTail)
                 pseudoRemainderGo fuel (remaining - 1) divisor next
             | _, _ => none)
    dsimp only
    rw [trimLeadingR_eq, listLenR_eq, listLenR_eq, blt_eq_decide]
    generalize trimLeading dividend = td
    by_cases hlt : td.length < divisor.length
    · simp only [hlt, decide_true, if_true]
      rw [scalePolynomialR_eq, intPowR_eq, headDR_eq]
      cases remaining with
      | zero =>
        change some td = some (scalePolynomial ((divisor.headD 0) ^ 0) td)
        rw [Int.pow_zero]
        exact congrArg some (scalePolynomial_one td).symm
      | succ r => rfl
    · simp only [hlt, decide_false, if_false]
      cases divisor with
      | nil => rfl
      | cons lcG divisorTail =>
        cases td with
        | nil => rfl
        | cons lcR dividendTail =>
          dsimp only
          rw [cancelPseudoLeadingR_eq, trimLeadingR_eq, pseudoRemainderGoR_eq fuel]
          rfl

noncomputable def pseudoRemainderR (dividend divisor : List Int) : Option (List Int) :=
  let dividend := trimLeadingR dividend
  let divisor := trimLeadingR divisor
  @List.casesOn Int (fun _ => Option (List Int)) divisor
    none
    (fun _ _ =>
      let lenDivd := listLenR dividend
      let lenDivs := listLenR divisor
      @Bool.rec (fun _ => Option (List Int))
        (pseudoRemainderGoR (Nat.add lenDivd (nat_lit 1))
          (Nat.add (Nat.sub lenDivd lenDivs) (nat_lit 1)) divisor dividend)
        (some dividend)
        (Nat.ble (Nat.add lenDivd (nat_lit 1)) lenDivs))

theorem pseudoRemainderR_eq (dividend divisor : List Int) :
    pseudoRemainderR dividend divisor = pseudoRemainder dividend divisor := by
  unfold pseudoRemainderR pseudoRemainder
  dsimp only
  rw [trimLeadingR_eq dividend, trimLeadingR_eq divisor]
  cases h : trimLeading divisor with
  | nil => rfl
  | cons d ds =>
    dsimp only
    rw [← h, listLenR_eq, listLenR_eq, blt_eq_decide, pseudoRemainderGoR_eq]
    have hempty : (trimLeading divisor).isEmpty = false := by rw [h]; rfl
    rw [hempty, if_neg (by decide)]
    by_cases hlt : (trimLeading dividend).length < (trimLeading divisor).length
    · simp only [hlt, decide_true, if_true]
    · simp only [hlt, decide_false, if_false]; rfl

noncomputable def exactDividePolynomialR (divisor : Int) : List Int → Option (List Int) :=
  @List.rec Int (fun _ => Option (List Int))
    (some [])
    (fun c _ ih =>
      @Bool.rec (fun _ => Option (List Int))
        (match ih with
         | none => none
         | some q => some (intEdivR c divisor :: q))
        none
        (@Bool.rec (fun _ => Bool)
          (@Bool.rec (fun _ => Bool) true false (intBeqZeroR (intEmodR c divisor)))
          true
          (intBeqZeroR divisor)))

theorem exactDividePolynomialR_eq (divisor : Int) : ∀ l : List Int,
    exactDividePolynomialR divisor l = exactDividePolynomial divisor l
  | [] => rfl
  | c :: cs => by
    show @Bool.rec (fun _ => Option (List Int))
      (match exactDividePolynomialR divisor cs with
       | none => none
       | some q => some (intEdivR c divisor :: q))
      none
      (@Bool.rec (fun _ => Bool)
        (@Bool.rec (fun _ => Bool) true false (intBeqZeroR (intEmodR c divisor)))
        true
        (intBeqZeroR divisor)) = exactDividePolynomial divisor (c :: cs)
    rw [exactDividePolynomial, intBeqZeroR_eq divisor, intEmodR_eq, intBeqZeroR_eq (c % divisor),
        intEdivR_eq, exactDividePolynomialR_eq divisor cs]
    have hbne : (c % divisor != 0) = !(c % divisor == 0) := rfl
    rw [hbne]
    cases (divisor == 0) <;> cases (c % divisor == 0) <;> rfl

noncomputable def normalResultantGoR :
    Nat → Bool → List Int → List Int → Option Int :=
  @Nat.rec (fun _ => Bool → List Int → List Int → Option Int)
    (fun _ _ _ => none)
    (fun _ ih initial f g =>
      match pseudoRemainderR f g with
      | none => none
      | some raw =>
        let divided :=
          @Bool.rec (fun _ => Option (List Int))
            (exactDividePolynomialR (intSqR (headDR (Int.ofNat (nat_lit 0)) f)) raw)
            (some raw)
            initial
        match divided with
        | none => none
        | some coefficients =>
          match trimLeadingR coefficients with
          | [] => some (Int.ofNat (nat_lit 0))
          | c :: cs =>
            let remainder := c :: cs
            @Bool.rec (fun _ => Option Int)
              none
              (@List.casesOn Int (fun _ => Option Int) cs
                (some c)
                (fun _ _ => ih false g remainder))
              (Nat.beq (Nat.add (listLenR remainder) (nat_lit 1)) (listLenR g)))

theorem normalResultantGoR_eq : ∀ (fuel : Nat) (initial : Bool) (f g : List Int),
    normalResultantGoR fuel initial f g = normalResultantGo fuel initial f g
  | 0, _, _, _ => rfl
  | fuel + 1, initial, f, g => by
    show (match pseudoRemainderR f g with
          | none => none
          | some raw =>
            let divided :=
              @Bool.rec (fun _ => Option (List Int))
                (exactDividePolynomialR (intSqR (headDR (Int.ofNat (nat_lit 0)) f)) raw)
                (some raw)
                initial
            match divided with
            | none => none
            | some coefficients =>
              match trimLeadingR coefficients with
              | [] => some (Int.ofNat (nat_lit 0))
              | c :: cs =>
                let remainder := c :: cs
                @Bool.rec (fun _ => Option Int)
                  none
                  (@List.casesOn Int (fun _ => Option Int) cs
                    (some c)
                    (fun _ _ => normalResultantGoR fuel false g remainder))
                  (Nat.beq (Nat.add (listLenR remainder) (nat_lit 1)) (listLenR g))) =
          normalResultantGo (fuel + 1) initial f g
    rw [normalResultantGo, pseudoRemainderR_eq]
    cases pseudoRemainder f g with
    | none => rfl
    | some raw =>
      dsimp only
      have hdiv : (@Bool.rec (fun _ => Option (List Int))
          (exactDividePolynomialR (intSqR (headDR (Int.ofNat 0) f)) raw)
          (some raw) initial) =
          (if initial then some raw else exactDividePolynomial ((f.headD 0) ^ 2) raw) := by
        rw [headDR_eq, intSqR_eq, exactDividePolynomialR_eq]
        cases initial <;> rfl
      rw [hdiv]
      cases (if initial then some raw else exactDividePolynomial ((f.headD 0) ^ 2) raw) with
      | none => rfl
      | some coefficients =>
        dsimp only
        rw [trimLeadingR_eq]
        cases hrem : trimLeading coefficients with
        | nil => rfl
        | cons c cs =>
          dsimp only
          rw [listLenR_eq, listLenR_eq, beq_eq_beq]
          cases ((c :: cs).length + 1 == g.length)
          · rfl
          · dsimp only
            cases cs with
            | nil => rfl
            | cons c2 cs2 =>
              dsimp only
              exact normalResultantGoR_eq fuel false g (c :: c2 :: cs2)

noncomputable def normalResultantR (f g : List Int) : Option Int :=
  let f := trimLeadingR f
  let g := trimLeadingR g
  @List.casesOn Int (fun _ => Option Int) g
    none
    (fun _ _ =>
      let lenF := listLenR f
      let lenG := listLenR g
      @Bool.rec (fun _ => Option Int)
        none
        (normalResultantGoR (Nat.add lenG (nat_lit 1)) true f g)
        (Nat.beq lenF (Nat.add lenG (nat_lit 1))))

theorem normalResultantR_eq (f g : List Int) :
    normalResultantR f g = normalResultant f g := by
  unfold normalResultantR normalResultant
  dsimp only
  rw [trimLeadingR_eq f, trimLeadingR_eq g]
  cases hg : trimLeading g with
  | nil =>
    simp
  | cons g0 gs =>
    dsimp only
    rw [← hg, listLenR_eq, listLenR_eq, beq_eq_beq, normalResultantGoR_eq]
    have hempty : (trimLeading g).isEmpty = false := by rw [hg]; rfl
    rw [hempty]
    cases ((trimLeading f).length == (trimLeading g).length + 1) <;> rfl

/-! ### Part 4: Raw polynomial generator (`polyOfR`, `derivHLR`) -/

def lcgNextR (state : Nat) : Nat :=
  Nat.mod (Nat.add (Nat.mul (nat_lit 6364136223846793005) state) (nat_lit 1442695040888963407))
    (nat_lit 18446744073709551616)

theorem lcgNextR_eq (state : Nat) : lcgNextR state = lcgNext state := rfl

def lcgSeedR (n : Nat) : Nat :=
  Nat.mod (Nat.add (Nat.mul (nat_lit 6364136223846793005) (Nat.add n (nat_lit 1))) (nat_lit 1442695040888963407))
    (nat_lit 18446744073709551616)

theorem lcgSeedR_eq (n : Nat) : lcgSeedR n = lcgSeed n := rfl

noncomputable def kbitsOfR (n : Nat) : Nat :=
  @Bool.rec (fun _ => Nat)
    (@Bool.rec (fun _ => Nat)
      (@Bool.rec (fun _ => Nat)
        (@Bool.rec (fun _ => Nat)
          (nat_lit 3484)
          (nat_lit 1001)
          (Nat.ble (Nat.add n (nat_lit 1)) (nat_lit 72057594037927936)))
        (nat_lit 205)
        (Nat.ble (Nat.add n (nat_lit 1)) (nat_lit 70368744177664)))
      (nat_lit 36)
      (Nat.ble (Nat.add n (nat_lit 1)) (nat_lit 68719476736)))
    (nat_lit 15)
    (Nat.ble (Nat.add n (nat_lit 1)) (nat_lit 67108864))

theorem kbitsOfR_eq (n : Nat) : kbitsOfR n = kbitsOf n := by
  unfold kbitsOfR kbitsOf difficultyLevel
  rw [blt_eq_decide n 67108864, blt_eq_decide n 68719476736,
      blt_eq_decide n 70368744177664, blt_eq_decide n 72057594037927936]
  by_cases h1 : n < 67108864
  · simp [h1]
  · by_cases h2 : n < 68719476736
    · simp [h1, h2]
    · by_cases h3 : n < 70368744177664
      · simp [h1, h2, h3]
      · by_cases h4 : n < 72057594037927936
        · simp [h1, h2, h3, h4]
        · simp [h1, h2, h3, h4]

noncomputable def clampWidthR (k width : Nat) : Nat :=
  let m := @Bool.rec (fun _ => Nat) width (nat_lit 2) (Nat.ble width (nat_lit 2))
  @Bool.rec (fun _ => Nat) m k (Nat.ble k m)

theorem clampWidthR_eq (k width : Nat) : clampWidthR k width = clampWidth k width := by
  unfold clampWidthR clampWidth
  dsimp only
  have hmax : @Bool.rec (fun _ => Nat) width 2 (Nat.ble width 2) = max 2 width := by
    rw [ble_eq_decide width 2, Nat.max_def]
    by_cases h : 2 ≤ width
    · by_cases hw : width ≤ 2
      · have : width = 2 := by omega
        subst this; rfl
      · simp [h, hw]
    · have hw : width ≤ 2 := by omega
      simp [h, hw]
  rw [hmax, ble_eq_decide k (max 2 width), Nat.min_def]
  by_cases hk : k ≤ max 2 width <;> simp [hk]

theorem hadd_eq (a b : Nat) : Nat.add a b = a + b := rfl
theorem hsub_eq (a b : Nat) : Nat.sub a b = a - b := rfl
theorem hmul_eq (a b : Nat) : Nat.mul a b = a * b := rfl
theorem hdiv_eq (a b : Nat) : Nat.div a b = a / b := rfl

noncomputable def coefficientWidthR (k i : Nat) : Nat :=
  @Bool.rec (fun _ => Nat)
    (let numerator := Nat.mul (Nat.sub k (nat_lit 3))
       (Nat.sub (Nat.mul (Nat.mul (nat_lit 102) (nat_lit 24)) i) (Nat.mul (Nat.mul (nat_lit 2) i) i))
     let denominator := Nat.mul (nat_lit 100) (nat_lit 576)
     clampWidthR k (Nat.add (nat_lit 3) (Nat.div (Nat.sub (Nat.add numerator denominator) (nat_lit 1)) denominator)))
    (let base := Nat.div (Nat.mul (nat_lit 2) (Nat.sub (nat_lit 36) k)) (nat_lit 7)
     let span := Nat.add (nat_lit 10) base
     clampWidthR k (Nat.add base (Nat.div (Nat.mul (Nat.sub k base) i) span)))
    (Nat.ble k (nat_lit 64))

theorem coefficientWidthR_eq (k i : Nat) : coefficientWidthR k i = coefficientWidth k i := by
  unfold coefficientWidthR coefficientWidth
  dsimp only
  rw [ble_eq_decide k 64]
  by_cases hk : k ≤ 64
  · simp only [hk, decide_true, if_true, hadd_eq, hsub_eq, hmul_eq, hdiv_eq]
    exact clampWidthR_eq _ _
  · simp only [hk, decide_false, if_false, hadd_eq, hsub_eq, hmul_eq, hdiv_eq]
    exact clampWidthR_eq _ _

noncomputable def collectCoeffWordR : Nat → Nat → Nat → Nat × Nat :=
  @Nat.rec (fun _ => Nat → Nat → Nat × Nat)
    (fun _ state => ((nat_lit 0), state))
    (fun _ ih shift state =>
      let state' := lcgNextR state
      let res := ih (Nat.add shift (nat_lit 64)) state'
      (Nat.add (Nat.shiftLeft state' shift) res.1, res.2))

theorem collectCoeffWordR_eq : ∀ words shift state,
    collectCoeffWordR words shift state = collectCoeffWord words shift state
  | 0, _, _ => rfl
  | words + 1, shift, state => by
    show (let state' := lcgNextR state
          let res := collectCoeffWordR words (Nat.add shift (nat_lit 64)) state'
          (Nat.add (Nat.shiftLeft state' shift) res.1, res.2)) =
         collectCoeffWord (words + 1) shift state
    rw [collectCoeffWord]
    dsimp only
    rw [lcgNextR_eq, collectCoeffWordR_eq words (shift + 64) (lcgNext state)]
    rcases collectCoeffWord words (shift + 64) (lcgNext state) with ⟨tail, finalState⟩
    dsimp only
    change (lcgNext state <<< shift + tail, finalState) = (lcgNext state * 2 ^ shift + tail, finalState)
    rw [Nat.shiftLeft_eq]

noncomputable def centeredNonzeroCoeffR (k words word : Nat) : Int :=
  let c := subNatR (Nat.shiftRight word (Nat.sub (Nat.mul (nat_lit 64) words) k))
                   (Nat.shiftLeft (nat_lit 1) (Nat.sub k (nat_lit 1)))
  @Bool.rec (fun _ => Int) c (Int.ofNat (nat_lit 1)) (intBeqZeroR c)

theorem centeredNonzeroCoeffR_eq (k words word : Nat) :
    centeredNonzeroCoeffR k words word = centeredNonzeroCoeff k words word := by
  unfold centeredNonzeroCoeffR centeredNonzeroCoeff
  dsimp only
  have hpow : Nat.shiftLeft (nat_lit 1) (Nat.sub k (nat_lit 1)) = 2 ^ (k - 1) := by
    change 1 <<< (k - 1) = 2 ^ (k - 1)
    rw [Nat.shiftLeft_eq, Nat.one_mul]
  have hsub : subNatR (Nat.shiftRight word (Nat.sub (Nat.mul (nat_lit 64) words) k))
      (Nat.shiftLeft (nat_lit 1) (Nat.sub k (nat_lit 1))) =
      Int.ofNat (word >>> (64 * words - k)) - Int.ofNat (2 ^ (k - 1)) := by
    rw [hpow, subNatR_eq, ofNat_sub_ofNat_eq]
    rfl
  rw [hsub, intBeqZeroR_eq]
  cases (Int.ofNat (word >>> (64 * words - k)) - Int.ofNat (2 ^ (k - 1)) == 0) <;> rfl

noncomputable def coefficientsFromR : Nat → Nat → Nat → Nat → List Int :=
  @Nat.rec (fun _ => Nat → Nat → Nat → List Int)
    (fun _ _ _ => [])
    (fun _ ih k index state =>
      let width := coefficientWidthR k index
      let words := Nat.div (Nat.add width (nat_lit 63)) (nat_lit 64)
      let ws := collectCoeffWordR words (nat_lit 0) state
      centeredNonzeroCoeffR width words ws.1 ::
        ih k (Nat.add index (nat_lit 1)) ws.2)

theorem coefficientsFromR_eq : ∀ count k index state,
    coefficientsFromR count k index state = coefficientsFrom count k index state
  | 0, _, _, _ => rfl
  | count + 1, k, index, state => by
    show (let width := coefficientWidthR k index
          let words := Nat.div (Nat.add width (nat_lit 63)) (nat_lit 64)
          let ws := collectCoeffWordR words (nat_lit 0) state
          centeredNonzeroCoeffR width words ws.1 ::
            coefficientsFromR count k (Nat.add index (nat_lit 1)) ws.2) =
         coefficientsFrom (count + 1) k index state
    rw [coefficientsFrom]
    dsimp only
    rw [coefficientWidthR_eq, collectCoeffWordR_eq, centeredNonzeroCoeffR_eq,
        coefficientsFromR_eq count]
    rfl

noncomputable def polyOfR (n : Nat) : List Int :=
  let k := kbitsOfR n
  Int.ofNat (nat_lit 1) :: coefficientsFromR (nat_lit 24) k (nat_lit 1) (lcgSeedR n)

theorem polyOfR_eq (n : Nat) : polyOfR n = polyOf n := by
  unfold polyOfR polyOf
  dsimp only
  rw [kbitsOfR_eq, lcgSeedR_eq, coefficientsFromR_eq]
  rfl

noncomputable def derivHLR (p : List Int) : List Int :=
  let degree := Nat.sub (listLenR p) (nat_lit 1)
  (List.range degree).map fun i =>
    intMulR (Int.ofNat (Nat.sub degree i)) (p.getD i (Int.ofNat (nat_lit 0)))

theorem derivHLR_eq (p : List Int) : derivHLR p = derivHL p := by
  unfold derivHLR derivHL
  rw [listLenR_eq]
  apply List.map_congr_left
  intro i _
  exact intMulR_eq _ _

theorem length_coefficientsFrom : ∀ count k index state,
    (coefficientsFrom count k index state).length = count
  | 0, _, _, _ => rfl
  | count + 1, k, index, state => by
    unfold coefficientsFrom
    dsimp only
    rw [List.length_cons, length_coefficientsFrom count]

theorem length_polyOf (n : Nat) : (polyOf n).length = 25 := by
  unfold polyOf
  rw [List.length_cons, length_coefficientsFrom]

noncomputable def impl (n : Nat) : Int :=
  let p := polyOfR n
  let derivative := derivHLR p
  match normalResultantR p derivative with
  | some resultant => resultant
  | none => bareissDet (monicReducedSylvester p derivative)

theorem impl_correct : ∀ n, impl n = discSpec n := by
  intro n
  unfold impl discSpec discriminantFromPoly resultantFromPoly
  dsimp only
  rw [polyOfR_eq, derivHLR_eq, normalResultantR_eq, length_polyOf]
  show _ = (if (25 - 1) * (25 - 1 - 1) / 2 % 2 = 0 then (1 : Int) else -1) * _
  rw [if_pos (by decide), Int.one_mul]
  rfl

end Submission
"""

DST.write_text(src)
print(f"wrote {DST} ({len(src)} bytes)")
