import Spec
import Submission
import LemmaA
import SumLen
import Bridge

namespace Probe2

/-- `(a :: l).drop d` has length `l.length + 1 - d`. -/
theorem length_drop_cons (a : Nat) (l : List Nat) (d : Nat) :
    ((a :: l).drop d).length = l.length + 1 - d := by
  cases d <;> simp

/-- `(a :: l).take d` has length `min d (l.length + 1)`. -/
theorem length_take_cons (a : Nat) (l : List Nat) (d : Nat) :
    ((a :: l).take d).length = min d (l.length + 1) := by
  cases d <;> simp

/-- A short block is terminal: the block list ends there. -/
theorem chunks_after_short (d fuel : Nat) (a : Nat) (l : List Nat)
    (hle : ¬ d ≤ l.length + 1) :
    Submission.chunks d fuel ((a :: l).drop d) = [] := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    cases hdrop_list : List.drop d (a :: l) with
    | nil => rfl
    | cons y ys =>
      have hdrop : ((a :: l).drop d).length = l.length + 1 - d :=
        length_drop_cons a l d
      have hzero : ((a :: l).drop d).length = 0 := by
        rw [hdrop]
        exact Nat.sub_eq_zero_of_le (Nat.le_of_not_ge hle)
      have hyy : (y :: ys).length = 0 := by
        rw [← hdrop_list]
        exact hzero
      simp at hyy

/-- The zipped block stream over `chunks d fuel l`, started from an accumulator
of length `d`, has `min (d * fuel) l.length` entries.

A full block keeps the accumulator at length `d`; a short block shrinks it, but
is necessarily the last one, so the shrinkage is terminal. -/
theorem length_zip_chunks : ∀ (fuel : Nat) (d : Nat) (p : List Nat) (l : List Nat),
    p.length = d →
    (Submission.zipBlocksAdd p (Submission.chunks d fuel l)).length
      = min (d * fuel) l.length := by
  intro fuel d p l hp
  induction fuel generalizing p l with
  | zero =>
    show (Submission.zipBlocksAdd p []).length = min (d * 0) l.length
    rw [Nat.mul_zero, Nat.min_eq_left (Nat.zero_le _)]
    rfl
  | succ fuel ih =>
    cases l with
    | nil =>
      show (Submission.zipBlocksAdd p []).length = min (d * (fuel + 1)) 0
      rw [Nat.min_eq_right (Nat.zero_le _)]
      rfl
    | cons a l =>
      have hunfold : Submission.chunks d (fuel + 1) (a :: l)
          = (a :: l).take d :: Submission.chunks d fuel ((a :: l).drop d) := rfl
      rw [hunfold, Submission.zipBlocksAdd, List.length_append]
      have htake : ((a :: l).take d).length = min d (l.length + 1) :=
        length_take_cons a l d
      have hlen : (a :: l).length = l.length + 1 := rfl
      by_cases hle : d ≤ l.length + 1
      · -- full block: the accumulator stays at length `d`, so `ih` applies
        have hp' : (Submission.addBlocks ((a :: l).take d) p).length = d := by
          have h := Probe.length_addBlocks ((a :: l).take d) p
          calc (Submission.addBlocks ((a :: l).take d) p).length
              = min (List.take d (a :: l)).length p.length := h
            _ = min d d := by rw [htake, hp, Nat.min_eq_left hle]
            _ = d := Nat.min_self _
        rw [ih (Submission.addBlocks ((a :: l).take d) p) ((a :: l).drop d) hp']
        rw [hp', hlen, length_drop_cons]
        by_cases h2 : d * fuel ≤ l.length + 1 - d
        · rw [Nat.min_eq_left h2, Nat.mul_succ]
          omega
        · rw [Nat.min_eq_right (Nat.le_of_not_ge h2), Nat.mul_succ]
          omega
      · -- short block: terminal, so the tail contributes nothing
        have hrest0 : Submission.chunks d fuel ((a :: l).drop d) = [] :=
          chunks_after_short d fuel a l hle
        rw [hrest0, hlen]
        -- the block itself is the whole remaining input
        have hshort : (Submission.addBlocks ((a :: l).take d) p).length = l.length + 1 := by
          have h := Probe.length_addBlocks ((a :: l).take d) p
          have h2 : min (List.take d (a :: l)).length p.length = l.length + 1 := by
            -- min (min d N) d with d ≥ N: the inner min is N, then N is the min
            have hmin : min d (l.length + 1) = l.length + 1 :=
              Nat.min_eq_right (Nat.le_of_not_ge hle)
            have hmin2 : min (l.length + 1) d = l.length + 1 := by
              rw [Nat.min_comm]
              exact hmin
            rw [htake, hp, hmin]
            exact hmin2
          exact h2 ▸ h
        rw [hshort, Submission.zipBlocksAdd]
        rw [Nat.mul_succ]
        have hN : min (d * fuel + d) (l.length + 1) = l.length + 1 := by
          have hge : l.length + 1 ≤ d * fuel + d := by
            have := hle
            omega
          exact Nat.min_eq_right hge
        rw [hN]
        omega

/-- The candidate's row update has the same length as its input. -/
theorem length_updRowAdd (d : Nat) (t : List Nat) (hd : 0 < d) :
    (Submission.updRowAdd d t).length = t.length := by
  unfold Submission.updRowAdd
  have hp : (List.replicate d 0).length = d := by simp
  rw [length_zip_chunks t.length d (List.replicate d 0) t hp]
  have hge : t.length ≤ d * t.length := by
    have hd1 : 1 ≤ d := Nat.succ_le_of_lt hd
    rw [Nat.mul_comm]
    exact Nat.le_mul_of_pos_right (n := t.length) hd1
  exact Nat.min_eq_right hge

end Probe2
