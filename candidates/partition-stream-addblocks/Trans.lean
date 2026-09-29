import Spec
import Submission
import LemmaA
import SumLen
import Bridge
import Len

namespace Probe

/-! ## Transport: `nthNat` reads like `getD` -/

/-- `nthNat` is `getD` with default `0`. -/
theorem nthNat_eq_getD : ∀ (t : List Nat) (m : Nat), Submission.nthNat t m = t.getD m 0 := by
  intro t
  induction t with
  | nil => intro m; cases m <;> rfl
  | cons x xs ih =>
    intro m
    cases m with
    | zero => rfl
    | succ m => exact ih m

end Probe
