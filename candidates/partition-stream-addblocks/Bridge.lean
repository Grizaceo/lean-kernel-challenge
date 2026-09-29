import Spec
import Submission
import LemmaA

/-!
Bridge file: the block-streaming row `updRowAdd` satisfies the *same*
pointwise recurrence as the reference `upd`, so the whole `partition-foldl`
scaffolding (`msum`, `rows_eq_partAux`, `impl_correct`) transfers verbatim.
-/

namespace Probe

/-- **The bridge lemma.** The candidate's tabled row update obeys precisely the
reference recurrence `upd f k m = f m + (if k+1 ≤ m then upd f k (m-(k+1)) else 0)`,
read off the materialized lists via `nthNat`.

This is `LemmaA.lemmaA` instantiated at `d := k + 1`. -/
theorem nthNat_updRowAdd (t : List Nat) (k m : Nat) (hm : m < t.length) :
    Submission.nthNat (Submission.updRowAdd (k + 1) t) m
      = (if k + 1 ≤ m
         then Submission.nthNat t m
                + Submission.nthNat (Submission.updRowAdd (k + 1) t) (m - (k + 1))
         else Submission.nthNat t m) := by
  have h := lemmaA (k + 1) t m (Nat.succ_pos k) hm
  by_cases hle : k + 1 ≤ m
  · rw [if_pos hle] at h
    rw [if_pos hle, h]
  · rw [if_neg hle] at h
    rw [if_neg hle, h]
    exact Nat.add_zero _

end Probe
