import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.MvPowerSeries.PiTopology
import Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries

/-!
# Verified Mathlib surface for the `partition` proof

Not a candidate. Contains no `sorry` and is never submitted: it only pins down
the exact signatures the `impl_correct` proof will rest on, so a future attempt
does not have to rediscover them. Every `example` below typechecks against the
Mathlib revision pinned in the challenge manifest.

Run with:  `cd problems/mertens && lake env lean EulerAPI.lean`

## Environment, since this cost real time to establish

* `Mathlib.Data.FPS` does not exist in this Mathlib. The univariate type is
  `PowerSeries R := MvPowerSeries (Fin 1) R`, in
  `Mathlib/RingTheory/PowerSeries/Basic.lean`, which is what defines the `⟦⟧`
  notation. Importing only `MvPowerSeries.Basic` gives you no `⟦⟧`.
* The inverse machinery is `MvPowerSeries/Inverse.lean`, not `Inv.lean`.
* `pentagonal` is at the ROOT namespace, not `Pentagonal.pentagonal`.
* The pentagonal theorem is `hasProd_one_sub_X_pow` (a `HasProd`); there is no
  `tprod_one_sub_X_pow`, and no bare `coeff_pentagonalSeries`.
* From-source `lake build` of these modules FAILS here
  (`Mathlib.Algebra.Algebra.Pi`). `lake exe cache get` is the only working way
  to get them: it produced 7364 files / 6.0 GB of complete `.olean`.

## What each piece is for

`hasProd_one_sub_X_pow` is Euler's pentagonal theorem, already formalised, and
`coeff_pentagonalSeries_*` is its coefficient-level form. `coeff_inv_aux` is the
coefficient recurrence for the inverse, and it is the step that turns the
product into a recurrence: with `phi = pentagonalSeries` (constant coefficient
1) it reads

    p(n) = - ∑ i in 1..n, (coeff i pentagonalSeries) * p(n-i)

which is Euler's sparse recurrence once the zero coefficients are used up.

## The chain, and what is still missing

    partAux (k+1) n = ∑ j, partAux k (n - j*(k+1))   -- the spec's recurrence
      = convolution of row k with (1 - X^(k+1))⁻¹     -- MISSING, see below
    => F k = .mk (partAux k) = ∏_{i≤k} (1 - X^i)⁻¹
    => F n = (∏' i, (1 - X^(i+1)))⁻¹ = (pentagonalSeries)⁻¹
    => coeff n of that = partAux n n = partitionSpec n
    => by coeff_inv_aux, partAux n n = - ∑ i, c_i * partAux (n-i) n

Missing and genuinely combinatorial: the first line's rewrite as a convolution,
and the telescoping from row `k` up to the infinite product. That rewrite is the
next thing to attack; the rest is API once it is done.
-/

open MvPowerSeries

section
variable {R : Type} [CommRing R]

-- The pentagonal numbers themselves. Note: root namespace, not `Pentagonal.`.
example (k : ℤ) : ℕ := pentagonal k

-- Off the pentagonal numbers the series has zero coefficient ...
example {n : ℕ} (h : n ∉ Set.range pentagonal) :
    (PowerSeries.pentagonalSeries R).coeff n = 0 :=
  PowerSeries.coeff_pentagonalSeries_eq_zero R h

-- ... and on them it is ±1.
example (k : ℤ) : (PowerSeries.pentagonalSeries R).coeff (pentagonal k) = Int.negOnePow k :=
  PowerSeries.coeff_pentagonalSeries_pentagonal R k

-- Euler's theorem. Needs the π-topology instance on `PowerSeries R`, which
-- lives in `MvPowerSeries/PiTopology.lean`; the `#check` pins the signature.
#check @PowerSeries.WithPiTopology.hasProd_one_sub_X_pow

-- Multiplication is coefficient convolution, which is how the spec's recurrence
-- becomes a statement about power series. Univariate `coeff` takes a plain
-- `n : ℕ` and the antidiagonal is over `ℕ × ℕ`, so no Finsupp index is needed
-- (the multivariate `MvPowerSeries.coeff_mul` is the same statement with the
-- index living in `Fin 1 →₀ ℕ`, and mixing the two does not typecheck).
example {n : ℕ} (φ ψ : PowerSeries R) :
    (φ * ψ).coeff n = ∑ p ∈ Finset.antidiagonal n, φ.coeff p.1 * ψ.coeff p.2 :=
  PowerSeries.coeff_mul n φ ψ

-- The inverse recurrence: Euler's sparse recurrence in disguise.
#check @MvPowerSeries.coeff_inv_aux
#check @MvPowerSeries.coeff_inv

end
