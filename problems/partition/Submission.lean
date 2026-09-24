import Spec

/-!
Integer partitions via coin-change DP.

`rows k m` counts partitions of `m` with parts ≤ k, computed by iterating
`upd` (adding one more allowed part size at a time). This mirrors the spec
recurrence `partAux` structurally, making correctness provable by induction.
-/

namespace Submission

/-- Adding part size `k+1` to the count function `f`:
`upd f k m = f m + upd f k (m - (k+1))` when `m ≥ k+1`, else `f m`. -/
def upd (f : Nat → Nat) (k m : Nat) : Nat :=
  if k + 1 ≤ m then f m + upd f k (m - (k + 1)) else f m
termination_by m
decreasing_by
  rename_i h
  exact Nat.sub_lt (Nat.lt_of_lt_of_le (Nat.succ_pos k) h) (Nat.succ_pos k)

/-- `rows k` = number of partitions into parts ≤ k, as a function of the total. -/
def rows : Nat → (Nat → Nat)
  | 0 => fun m => if m = 0 then 1 else 0
  | k + 1 => upd (rows k) k

def impl (n : Nat) : Nat := rows n n

/-! ### Helper lemmas -/

/-- Sum of `f` over `List.range M`, exactly the spec's map+foldl shape. -/
def msum (f : Nat → Nat) (M : Nat) : Nat :=
  ((List.range M).map f).foldl (· + ·) 0

theorem msum_succ (f : Nat → Nat) (M : Nat) :
    msum f (M + 1) = msum f M + f M := by
  unfold msum
  rw [List.range_succ, List.map_append, List.foldl_append]
  simp [List.foldl]

theorem msum_congr {f g : Nat → Nat} (M : Nat) (h : ∀ j, j < M → f j = g j) :
    msum f M = msum g M := by
  induction M with
  | zero => rfl
  | succ M ih =>
    rw [msum_succ, msum_succ, h M (Nat.lt_succ_self M),
        ih (fun j hj => h j (Nat.lt_trans hj (Nat.lt_succ_self M)))]

/-- Shift identity for truncated subtraction:
`(m - d) - j*d = m - (j+1)*d`. -/
theorem sub_sub_eq (m d j : Nat) : (m - d) - j * d = m - (j + 1) * d := by
  rw [Nat.sub_sub, Nat.add_mul, Nat.one_mul, Nat.add_comm d (j * d)]

theorem msum_zero (f : Nat → Nat) : msum f 0 = 0 := rfl

/-- Peel the front term of the multiplicity sum:
sum over `j < M+1` of `f (m - j*d)` equals `f m` plus the shifted sum. -/
theorem msum_peel (f : Nat → Nat) (d : Nat) :
    ∀ m M, msum (fun j => f (m - j * d)) (M + 1)
         = f m + msum (fun i => f (m - (i + 1) * d)) M := by
  intro m M
  induction M with
  | zero =>
    rw [msum_succ]
    show msum (fun j => f (m - j * d)) 0 + f (m - 0 * d) = f m + msum _ 0
    rw [msum_zero, msum_zero]
    have h : m - 0 * d = m := by simp
    rw [h]
    omega
  | succ M ih =>
    rw [msum_succ, ih, msum_succ]
    omega

/-- Characterization of `upd f k` as the sum over multiplicities `j`
of the new part size `d = k+1`: exactly the spec's shape. -/
theorem upd_eq_msum (f : Nat → Nat) (d : Nat) (hd : 0 < d) :
    ∀ m, upd f (d - 1) m = msum (fun j => f (m - j * d)) (m / d + 1) := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
    have hdS : d - 1 + 1 = d := Nat.sub_add_cancel (Nat.succ_le_of_lt hd)
    unfold upd
    rw [hdS]
    by_cases h : d ≤ m
    · rw [if_pos h]
      generalize hm' : m - d = m'
      have hm : m = m' + d := by rw [← hm']; exact (Nat.sub_add_cancel h).symm
      have hlt : m' < m := by rw [← hm']; exact Nat.sub_lt (Nat.lt_of_lt_of_le hd h) hd
      have ih' := ih m' hlt
      have hdiv : m / d = m' / d + 1 := by
        have this : m' + d - d = m' := Nat.add_sub_cancel m' d
        rw [hm, Nat.div_eq, if_pos ⟨hd, Nat.le_add_left d m'⟩, this]
      rw [hdiv, msum_peel, ih']
      have cong : msum (fun i => f (m' - i * d)) (m' / d + 1)
                = msum (fun i => f (m - (i + 1) * d)) (m' / d + 1) := by
        apply msum_congr
        intro i _
        rw [← hm', sub_sub_eq m d i]
      rw [← cong, ← ih']
    · rw [if_neg h]
      have hdiv0 : m / d = 0 := by
        rw [Nat.div_eq]
        exact if_neg (fun ⟨_, hle⟩ => h hle)
      rw [hdiv0, msum_succ, msum_zero]
      have h0 : m - 0 * d = m := by simp
      rw [h0]
      omega

/-- `rows` computes `partAux` exactly. -/
theorem rows_eq_partAux : ∀ k m, rows k m = partAux k m := by
  intro k
  induction k with
  | zero =>
    intro m
    cases m with
    | zero => rfl
    | succ m => rfl
  | succ k ih =>
    intro m
    show upd (rows k) k m = partAux (k + 1) m
    have h := upd_eq_msum (rows k) (k + 1) (Nat.succ_pos k) m
    rw [Nat.add_sub_cancel] at h
    rw [h]
    show msum (fun j => rows k (m - j * (k + 1))) (m / (k + 1) + 1)
       = ((List.range (m / (k + 1) + 1)).map
            (fun j => partAux k (m - j * (k + 1)))).foldl (· + ·) 0
    exact msum_congr _ (fun j _ => ih (m - j * (k + 1)))

theorem impl_correct : ∀ n, impl n = partitionSpec n := by
  intro n
  show rows n n = partAux n n
  exact rows_eq_partAux n n

end Submission
