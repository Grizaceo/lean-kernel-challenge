import Spec
import Submission
import LemmaA

namespace Probe

/-- Every block produced by `chunks` is at most `d` long. -/
theorem chunks_blocks_le (d : Nat) : ∀ (fuel : Nat) (l : List Nat) (b : List Nat),
    b ∈ Submission.chunks d fuel l → b.length ≤ d := by
  intro fuel
  induction fuel with
  | zero => intro l b h; cases h
  | succ fuel ih =>
    intro l b h
    have hnil : Submission.chunks d (fuel+1) ([] : List Nat) = [] := rfl
    cases l with
    | nil =>
        rw [hnil] at h
        cases h
    | cons a l =>
      rw [show Submission.chunks d (fuel+1) (a :: l)
             = (a :: l).take d :: Submission.chunks d fuel ((a :: l).drop d) from rfl] at h
      simp only [List.mem_cons] at h
      cases h with
      | inl heq =>
        cases heq
        have hlen : (List.take d (a :: l)).length = min d (l.length + 1) := by
          simp [List.length_take]
        rw [hlen]
        exact Nat.min_le_left _ _
      | inr hrest => exact ih ((a :: l).drop d) b hrest

/-- The total block count produced by `chunks d fuel l`. -/
def sumLen : List (List Nat) → Nat
  | [] => 0
  | b :: rest => b.length + sumLen rest

theorem sumLen_chunks_nil (d fuel : Nat) :
    sumLen (Submission.chunks d (fuel+1) ([] : List Nat)) = min (d * (fuel+1)) 0 := by
  have h1 : (Submission.chunks d (fuel+1) ([] : List Nat)) = [] := rfl
  rw [h1, sumLen, Nat.min_eq_right (Nat.zero_le _)]

theorem sumLen_chunks_cons (d fuel : Nat) (a : Nat) (l : List Nat)
    (ih : ∀ (m : List Nat), sumLen (Submission.chunks d fuel m) = min (d * fuel) m.length) :
    sumLen (Submission.chunks d (fuel+1) (a :: l)) = min (d * (fuel+1)) (l.length + 1) := by
  have hdrop : ((a :: l).drop d).length = l.length + 1 - d := by
    cases d with
    | zero => simp
    | succ d => simp
  have htake : ((a :: l).take d).length = min d (l.length + 1) := by
    cases d with
    | zero => simp
    | succ d => simp
  have hchunks : Submission.chunks d (fuel+1) (a :: l)
      = (a :: l).take d :: Submission.chunks d fuel ((a :: l).drop d) := rfl
  rw [hchunks, sumLen, htake, ih, hdrop]
  by_cases hd0 : d = 0
  · rw [hd0]
    have h1 : min 0 (l.length + 1) = 0 := Nat.min_eq_left (Nat.zero_le _)
    have h2 : min (0 * fuel) (l.length + 1 - 0) = 0 := by
      rw [Nat.zero_mul, Nat.sub_zero, Nat.min_eq_left (Nat.zero_le _)]
    have h3 : min (0 * (fuel + 1)) (l.length + 1) = 0 := by
      rw [Nat.zero_mul, Nat.min_eq_left (Nat.zero_le _)]
    rw [h1, h2, h3]
  · by_cases hle : d ≤ l.length + 1
    · by_cases hdf : d * fuel ≤ l.length + 1 - d
      · rw [Nat.min_eq_left hle, Nat.min_eq_left hdf, Nat.mul_add, Nat.mul_one,
            Nat.add_comm, Nat.min_eq_left (by omega)]
      · have hc : l.length + 1 - d + d = l.length + 1 := Nat.sub_add_cancel hle
        rw [Nat.min_eq_left hle, Nat.min_eq_right (by omega), Nat.mul_add,
            Nat.mul_one, Nat.add_comm, hc, Nat.min_eq_right (by omega)]
    · have hm : d * (fuel + 1) = d * fuel + d := by
        rw [Nat.mul_add, Nat.mul_one]
      rw [hm, Nat.min_eq_right (Nat.le_of_not_ge hle)]
      have hz : l.length + 1 - d = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_not_ge hle)
      have hmf : min (d * fuel) (l.length + 1 - d) = 0 := by
        rw [hz, Nat.min_eq_right (Nat.zero_le _)]
      rw [hmf, Nat.add_zero, Nat.min_eq_right (by omega)]

theorem sumLen_chunks (d : Nat) : ∀ (fuel : Nat) (l : List Nat),
    sumLen (Submission.chunks d fuel l) = min (d * fuel) l.length := by
  intro fuel
  induction fuel with
  | zero => intro l; simp [Submission.chunks, sumLen, Nat.mul_zero, Nat.min_eq_left]
  | succ fuel ih =>
    intro l
    cases l with
    | nil => exact sumLen_chunks_nil d fuel
    | cons a l =>
      rw [show (a :: l).length = l.length + 1 from rfl]
      rw [sumLen_chunks_cons d fuel a l ih]

end Probe
