import Spec
import Submission
import LemmaA
import SumLen
import Bridge
import Len
import Trans
import Msum
import Char
import Correct
import Coin

namespace Probe

/-! ## Tying the streaming rows to `partAux`

`itAdd` applies the row steps in *decreasing* part size: `itAdd (k+1) t` is
`itAdd k (updRowAdd (k+1) t)`, so size `k+1` is applied first and size `1`
last. The spec's `partAux` recurrence instead wants one step per `k`, in
increasing order.

The bridge is `Coin.lean`: the row-step operators commute, so the order is
irrelevant. That lets the decreasing iteration be rewritten as the increasing
one, and `inv_step` then carries the invariant from `partAux 0` to `partAux n`.

`nthNat_updRowAdd_eq_msum` is stated for `m < t.length`, so the invariant is
carried together with the length: the table must be long enough for every
column the invariant talks about. -/

/-- `msum` is definitionally the spec's inner sum, so the streaming row step
`nthNat_updRowAdd_eq_msum` is exactly `partAux`'s unfolding. This is the
equation the whole proof is built on. -/
theorem partAux_eq_msum (k : Nat) (n : Nat) :
    partAux (k + 1) n
      = msum (fun j => partAux k (n - j * (k + 1))) (n / (k + 1) + 1) := rfl

/-- The empty partition is counted once, at every part size. -/
theorem partAux_zero (k : Nat) : partAux k 0 = 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show msum (fun j => partAux k (0 - j * (k + 1))) (0 / (k + 1) + 1) = 1
    have hz : 0 / (k + 1) = 0 := by simp
    -- the range is 0 / (k+1) + 1, so `msum_succ` peels off the single term
    rw [hz, Nat.zero_add, msum_succ, msum_zero, Nat.add_zero]
    have heq : 0 - 0 * (k + 1) = 0 := by simp
    rw [heq, ih]

/-- Column invariant after `k` row steps, stated for a *function* so it does
not depend on how the table is represented. `f` is the column-reading
function of the table; `len` is that table's length, and the invariant is
only claimed for columns below it. -/
def Inv (k : Nat) (len : Nat) (f : Nat → Nat) : Prop :=
  ∀ m, m < len → f m = if m = 0 then 1 else partAux k m

/-- The initial table satisfies the invariant for `k = 0`: every column is `0`
except column `0`, which is `1`, and `partAux 0 m = 0` for `m ≠ 0`. -/
theorem inv_init (n : Nat) :
    Inv 0 (Submission.initTable n).length
      (Submission.nthNat (Submission.initTable n)) := by
  intro m hm
  have hcons : Submission.initTable n = 1 :: List.replicate n 0 := rfl
  by_cases hz : m = 0
  · -- column 0 is the head of the table, and it is 1
    rw [hz, if_pos rfl, hcons]
    rfl
  · -- every other column is a zero, and `partAux 0 m = 0` there
    have hpos : 0 < m := Nat.pos_of_ne_zero hz
    rw [hcons, nthNat_getD, if_neg hz]
    show (1 :: List.replicate n 0).getD m 0 = partAux 0 m
    -- `m > 0`, so `getD` steps past the head into the zeros
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_lt hpos)
    -- the table is `1` followed by `n` zeros, so any column past 0 reads a zero
    -- the head was already stepped over, so the read lands in the replicate of
    -- zeros, which is 0
    -- normalise the index in both the goal and the hypotheses, then destructure
    -- it as a successor (`hpos` guarantees the successor shape)
    simp only [Nat.zero_add] at hz hpos ⊢
    obtain ⟨j, hk⟩ := Nat.exists_eq_succ_of_ne_zero hz
    rw [hk]
    show (1 :: List.replicate n 0).getD (j + 1) 0 = partAux 0 (j + 1)
    -- the RHS is `partAux 0 (j+1)`, which is the same column as `partAux 0 j`
    -- because `partAux k m` does not depend on m
    rw [List.getD_cons_succ]
    have hz1 := nthNat_replicate_zero n j
    rw [nthNat_getD] at hz1
    rwa [List.getD_eq_getElem?_getD] at hz1

/-- One row step advances the invariant. The row step is the spec's sum over
multiplicities, and each summand is the predecessor column, which the
hypothesis already identifies with `partAux k`. The `m = 0` term is the one
place the "always 1" convention matters, and `partAux_zero` reconciles it.

The length is preserved by `length_updRowAdd`, and `updRowAdd` needs `0 < d`,
which is why this is stated at `k + 1`. -/
theorem inv_step (k : Nat) (len : Nat) (f : Nat → Nat) (h : Inv k len f) :
    Inv (k + 1) len (T (k + 1) f) := by
  intro m hm
  -- every column the step reads is at most m, hence in range
  have hsub : ∀ j, j * (k + 1) ≤ m → m - j * (k + 1) < len := by
    intro j hj
    have h2 : m - j * (k + 1) ≤ m := Nat.sub_le _ _
    have h3 : m < len := hm
    omega
  unfold T
  by_cases hz : m = 0
  · rw [if_pos hz]
    -- column 0 stays 1: the only summand is f 0
    show msum (fun j => f (m - j * (k + 1))) (m / (k + 1) + 1) = 1
    -- the range is m / (k+1) + 1, and with m = 0 that is 0 + 1, so `msum_succ`
    -- peels off the single summand, which reads column 0
    subst hz
    have hq : 0 / (k + 1) = 0 := by simp
    have hq' : 0 - 0 * (k + 1) = 0 := by simp
    rw [hq, Nat.zero_add, msum_succ, msum_zero, Nat.add_zero, hq']
    have h0 := h 0 (by omega)
    rw [if_pos rfl] at h0
    omega
  · rw [if_neg hz]
    show msum (fun j => f (m - j * (k + 1))) (m / (k + 1) + 1) = partAux (k + 1) m
    rw [partAux_eq_msum]
    refine msum_congr _ ?_
    intro j hj
    -- `j < m / (k+1) + 1` is exactly `j * (k+1) ≤ m`
    have hjle : j * (k + 1) ≤ m := by
      have hlt : j < m / (k + 1) + 1 := hj
      have h2 : j ≤ m / (k + 1) := by omega
      exact Nat.mul_le_of_le_div (k + 1) j m h2
    have hsub' := hsub j hjle
    have hc := h (m - j * (k + 1)) hsub'
    by_cases hzero : m - j * (k + 1) = 0
    · -- the predecessor column is the "empty partition" column, and both
      -- the invariant and `partAux_zero` call it 1
      have hc0 := h (m - j * (k + 1)) hsub'
      rw [hzero, if_pos rfl] at hc0
      rw [hzero, hc0]
      exact (partAux_zero k).symm
    · rw [if_neg hzero] at hc
      exact hc

end Probe
