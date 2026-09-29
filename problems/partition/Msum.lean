import Spec
import Submission
import LemmaA
import SumLen
import Bridge
import Len
import Trans

namespace Probe

/-! ## The msum scaffolding -/

def msum (f : Nat → Nat) (M : Nat) : Nat :=
  (List.range M).map f |>.foldl (· + ·) 0

theorem msum_succ (f : Nat → Nat) (M : Nat) :
    msum f (M + 1) = msum f M + f M := by
  unfold msum
  rw [List.range_succ, List.map_append, List.foldl_append]
  rfl

theorem msum_congr {f g : Nat → Nat} (M : Nat) (h : ∀ j, j < M → f j = g j) :
    msum f M = msum g M := by
  induction M with
  | zero => rfl
  | succ M ih =>
    rw [msum_succ, msum_succ, h M (Nat.lt_succ_self M)]
    rw [ih (fun j hj => h j (Nat.lt_trans hj (Nat.lt_succ_self M)))]

theorem msum_zero (f : Nat → Nat) : msum f 0 = 0 := rfl

theorem msum_peel (f : Nat → Nat) (d : Nat) :
    ∀ m M, msum (fun j => f (m - j * d)) (M + 1)
         = f m + msum (fun i => f (m - (i + 1) * d)) M := by
  intro m M
  induction M with
  | zero =>
    rw [Nat.zero_add]
    show msum (fun j => f (m - j * d)) 1 = f m + msum (fun i => f (m - (i + 1) * d)) 0
    rw [msum_succ]
    show msum (fun j => f (m - j * d)) 0 + f (m - 0 * d)
      = f m + msum (fun i => f (m - (i + 1) * d)) 0
    rw [show msum (fun j => f (m - j * d)) 0 = 0 from msum_zero (fun j => f (m - j * d)),
        show msum (fun i => f (m - (i + 1) * d)) 0 = 0 from msum_zero (fun i => f (m - (i + 1) * d)),
        Nat.zero_mul, Nat.zero_add, Nat.add_zero, Nat.sub_zero]
  | succ M ih =>
    show msum (fun j => f (m - j * d)) (M + 1 + 1)
      = f m + msum (fun i => f (m - (i + 1) * d)) (M + 1)
    rw [show M + 1 + 1 = Nat.succ (Nat.succ M) from rfl]
    rw [msum_succ, ih, msum_succ, Nat.add_assoc]

end Probe
