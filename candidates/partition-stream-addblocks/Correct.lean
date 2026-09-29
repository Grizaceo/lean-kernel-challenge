import Spec
import Submission
import LemmaA
import SumLen
import Bridge
import Len
import Trans
import Msum
import Char

namespace Probe

/-! ## The row step is the reference row step -/

/-- `updRowAdd d t` reads, at column `m`, exactly the reference `upd` step on
the predecessor row.

`Bridge.nthNat_updRowAdd` gives the recurrence for the streaming row; the
reference recurrence differs only in the guard, which `d > 0` normalises via
`d - 1 + 1 = d`. Induction is on `m` because the recurrence recurses at `m - d`. -/
theorem nthNat_updRowAdd_eq_updRef (d : Nat) (hd : 0 < d) :
    ∀ (t : List Nat) (m : Nat), m < t.length →
      Submission.nthNat (Submission.updRowAdd d t) m
        = updRef (Submission.nthNat t) (d - 1) m := by
  intro t m
  induction m using Nat.strongRecOn with
  | _ m ihm =>
    intro hm
    have hrec' : Submission.nthNat (Submission.updRowAdd d t) m
        = (if d ≤ m
           then Submission.nthNat t m
                  + Submission.nthNat (Submission.updRowAdd d t) (m - d)
           else Submission.nthNat t m) := by
      have h := nthNat_updRowAdd t (d - 1) m hm
      rw [Nat.sub_add_cancel hd] at h
      exact h
    by_cases hle : d ≤ m
    · have hle' : d - 1 + 1 ≤ m := by rw [Nat.sub_add_cancel hd]; exact hle
      unfold updRef
      rw [if_pos hle', Nat.sub_add_cancel hd, hrec', if_pos hle]
      -- the recursive occurrence is the same statement at the smaller column
      have hmlt : m - d < m := Nat.sub_lt (Nat.lt_of_lt_of_le hd hle) hd
      have hinner : m - d < t.length := by omega
      exact congrArg (fun z => Submission.nthNat t m + z) (ihm (m - d) hmlt hinner)
    · have hle' : ¬ d - 1 + 1 ≤ m := by
        rw [Nat.sub_add_cancel hd]
        exact hle
      unfold updRef
      rw [if_neg hle']
      rw [hrec', if_neg hle]

/-- Consequently the streaming row step is literally the spec's `msum` over
multiplicities of part size `d`. This is the characterisation that lets the
`partition-foldl` correctness argument transfer verbatim. -/
theorem nthNat_updRowAdd_eq_msum (d : Nat) (hd : 0 < d) :
    ∀ (t : List Nat) (m : Nat), m < t.length →
      Submission.nthNat (Submission.updRowAdd d t) m
        = msum (fun j => Submission.nthNat t (m - j * d)) (m / d + 1) := by
  intro t m hm
  rw [nthNat_updRowAdd_eq_updRef d hd t m hm]
  exact updRef_eq_msum (Submission.nthNat t) d hd (d - 1) m (Nat.sub_add_cancel hd)

end Probe
