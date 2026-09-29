import Spec
import Submission
import LemmaA
import SumLen
import Bridge
import Len
import Trans
import Msum

namespace Probe

/-! ## The reference characterisation, on `nthNat` rows -/

/-- Shift identity for truncated subtraction:
`(m - d) - j*d = m - (j+1)*d`. -/
theorem sub_sub_eq (m d j : Nat) : (m - d) - j * d = m - (j + 1) * d := by
  rw [Nat.sub_sub, Nat.add_mul, Nat.one_mul, Nat.add_comm d (j * d)]

/-- The reference recurrence over a column function, mirroring `Submission.upd`
from the foldl candidate: `k` counts already-accepted part sizes, so the new
part size is `k + 1`. -/
def updRef (f : Nat → Nat) (k : Nat) : Nat → Nat
  | m => if k + 1 ≤ m then f m + updRef f k (m - (k + 1)) else f m
termination_by m => m
decreasing_by
  rename_i h
  exact Nat.sub_lt (Nat.lt_of_lt_of_le (Nat.succ_pos k) h) (Nat.succ_pos k)

/-- Unrolling `updRef`: it is the sum over multiplicities `j` of part size
`d = k+1`, exactly the spec's `map`+`foldl` shape. -/
theorem updRef_eq_msum (f : Nat → Nat) (d : Nat) (hd : 0 < d) :
    ∀ k m, k + 1 = d → updRef f k m = msum (fun j => f (m - j * d)) (m / d + 1) := by
  intro k m hkd
  induction m using Nat.strongRecOn with
  | _ m ih =>
    by_cases h : k + 1 ≤ m
    · unfold updRef
      rw [if_pos h]
      rw [← hkd]
      generalize hm' : m - (k + 1) = m'
      have hmEq : m = m' + (k + 1) := by
        rw [← hm']
        exact (Nat.sub_add_cancel h).symm
      have hlt : m' < m := by
        rw [← hm']
        exact Nat.sub_lt (Nat.lt_of_lt_of_le (Nat.succ_pos k) h) (Nat.succ_pos k)
      have ih' := ih m' hlt
      have hdiv : m / (k + 1) = m' / (k + 1) + 1 := by
        have this : m' + (k + 1) - (k + 1) = m' := Nat.add_sub_cancel m' (k + 1)
        rw [hmEq, Nat.div_eq, if_pos ⟨hkd ▸ hd, Nat.le_add_left (k + 1) m'⟩, this]
      rw [hdiv, msum_succ, msum_peel, ih', Nat.add_comm]
      -- re-index the peeled sum back onto the predecessor row
      have cong : msum (fun i => f (m - (i + 1) * (k + 1))) (m' / (k + 1))
                = msum (fun i => f (m' - i * d)) (m' / d) := by
        rw [← hkd]
        apply msum_congr
        intro i _
        congr 1
        rw [← hm', sub_sub_eq m (k + 1) i]
      rw [cong]
      -- the residual `f m` is the `j = 0` term, which `hmEq` re-expresses
      have hlast : m - (m' / (k + 1) + 1) * (k + 1) = m' - (m' / (k + 1)) * (k + 1) := by
        rw [hmEq, Nat.add_mul, Nat.one_mul]
        omega
      rw [hlast, ← hkd, msum_succ]
      simp [Nat.add_comm, Nat.add_left_comm]
    · unfold updRef
      rw [if_neg h]
      rw [← hkd]
      have hdiv0 : m / (k + 1) = 0 := by
        rw [Nat.div_eq]
        exact if_neg (fun ⟨_, hle⟩ => h hle)
      rw [hdiv0, Nat.zero_add, msum_succ]
      simp [msum_zero, Nat.zero_mul]

end Probe
