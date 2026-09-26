import Spec

/-!
Integer partitions via coin-change DP with materialized rows.

The reference recursion `rows k m` (proved equal to `partAux`) re-reduces the
whole closure on every call, so `rows n n` costs ~ p(n)·n kernel steps.  The
tabled version below computes the same recurrence row by row as concrete
lists: `updRow d t` builds the new row from the materialized previous row
`t` by the multiplicity sum over `d`, so each cell is computed once.
Correctness: `updRow_correct` ties the tabled row to `rows` via the already
proved `upd_eq_msum`, and `tableItFrom` iterates over part sizes `j+1..j+k`.
-/

namespace Submission

/-- The reference (slow) recurrence; kept as the correctness anchor. -/
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

/-! ### Sum lemmas (spec shape) -/

/-- Sum of `f` over `List.range M`, exactly the spec's map+foldl shape. -/
def msum (f : Nat → Nat) (M : Nat) : Nat :=
  (List.range M).foldl (fun acc j => acc + f j) 0

theorem msum_succ (f : Nat → Nat) (M : Nat) :
    msum f (M + 1) = msum f M + f M := by
  unfold msum
  rw [List.range_succ, List.foldl_append]
  simp [List.foldl]

theorem msum_congr {f g : Nat → Nat} (M : Nat) (h : ∀ j, j < M → f j = g j) :
    msum f M = msum g M := by
  induction M with
  | zero => rfl
  | succ M ih =>
    rw [msum_succ, msum_succ, h M (Nat.lt_succ_self M),
        ih (fun j hj => h j (Nat.lt_trans hj (Nat.lt_succ_self M)))]

theorem msum_zero (f : Nat → Nat) : msum f 0 = 0 := rfl

/-- Shift identity for truncated subtraction:
`(m - d) - j*d = m - (j+1)*d`. -/
theorem sub_sub_eq (m d j : Nat) : (m - d) - j * d = m - (j + 1) * d := by
  rw [Nat.sub_sub, Nat.add_mul, Nat.one_mul, Nat.add_comm d (j * d)]

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

/-! ### Tabled rows -/

/-- The multiplicity sum for the new row, from the previous materialized row. -/
def rowSum (t : List Nat) (d m : Nat) : Nat :=
  msum (fun j => t.getD (m - j * d) 0) (m / d + 1)

/-- The new row for part size `d`: `u[m] = rowSum t d m`. -/
def updRow (d : Nat) (t : List Nat) : List Nat :=
  (List.range t.length).map (fun m => rowSum t d m)

/-- Initial row for parts ≤ 0: 1 at m=0, 0 elsewhere (length n+1). -/
def initTable (n : Nat) : List Nat := 1 :: List.replicate n 0

/-- Apply part sizes `j+1 .. j+k` to the current row `t`. -/
def tableItFrom (j : Nat) : Nat → List Nat → List Nat
  | 0, t => t
  | k + 1, t => tableItFrom (j + 1) k (updRow (j + 1) t)

def impl (n : Nat) : Nat := (tableItFrom 0 n (initTable n)).getD n 0

/-! ### Tabled-row correctness -/

/-- `getD` of a `range`-mapped list at index `m` is `f m`. -/
theorem getD_map_range (f : Nat → Nat) (L m : Nat) (hm : m < L) :
    ((List.range L).map f).getD m 0 = f m := by
  unfold List.getD
  rw [List.getElem?_map, List.getElem?_range hm]
  simp

/-- `getD` of `updRow`. -/
theorem updRow_getD (d : Nat) (t0 : List Nat) (m : Nat) (hm : m < t0.length) :
    (updRow d t0).getD m 0 = rowSum t0 d m := by
  unfold updRow
  exact getD_map_range (fun m => rowSum t0 d m) t0.length m hm

/-- A correct previous row yields a correct next row, tying `updRow` to `rows`. -/
theorem updRow_correct (t : List Nat) (k m : Nat) (hm : m < t.length)
    (hprev : ∀ x, x < t.length → t.getD x 0 = rows k x) :
    (updRow (k + 1) t).getD m 0 = rows (k + 1) m := by
  rw [updRow_getD (k + 1) t m hm]
  unfold rowSum
  change msum (fun j => t.getD (m - j * (k + 1)) 0) (m / (k + 1) + 1)
       = upd (rows k) k m
  have h := upd_eq_msum (rows k) (k + 1) (Nat.succ_pos k) m
  rw [Nat.add_sub_cancel] at h
  rw [h]
  apply msum_congr
  intro j _
  exact hprev (m - j * (k + 1)) (Nat.lt_of_le_of_lt (Nat.sub_le m (j * (k + 1))) hm)

/-- `List.replicate n 0` has getD 0 below `n`. -/
theorem replicate_getD_zero : ∀ n i, i < n → (List.replicate n 0).getD i 0 = 0 := by
  intro n
  induction n with
  | zero => intro i h; omega
  | succ n ih =>
    intro i h
    cases i with
    | zero => simp [List.replicate]
    | succ i =>
      have hi : i < n := by omega
      simp [List.replicate, List.getD]
      exact ih i hi

/-- Initial row at index `m`. -/
theorem initTable_getD (n m : Nat) (hm : m < n + 1) :
    (initTable n).getD m 0 = rows 0 m := by
  cases m with
  | zero => simp [initTable, rows]
  | succ m =>
    have hm' : m < n := by omega
    rw [show (initTable n).getD (m + 1) 0 = (List.replicate n 0).getD m 0 by
      simp [initTable, List.getD]]
    rw [replicate_getD_zero n m hm']
    simp [rows]

/-- Table invariant: starting from a row equal to `rows j` on `[0,n]`, applying
part sizes `j+1..j+k` yields `rows (j+k)` on the same domain. -/
theorem tableItFrom_correct (k j n : Nat) (t : List Nat) (ht : t.length = n + 1)
    (hrow : ∀ x, x < n + 1 → t.getD x 0 = rows j x) :
    ∀ m, m < n + 1 → (tableItFrom j k t).getD m 0 = rows (j + k) m := by
  revert j t ht hrow
  induction k with
  | zero =>
    intro j t ht hrow m hm
    change t.getD m 0 = rows (j + 0) m
    rw [Nat.add_zero]
    exact hrow m hm
  | succ k ih =>
    intro j t ht hrow m hm
    change (tableItFrom (j + 1) k (updRow (j + 1) t)).getD m 0 = rows (j + (k + 1)) m
    have hrow' : ∀ x, x < n + 1 → (updRow (j + 1) t).getD x 0 = rows (j + 1) x := by
      intro x hx
      exact updRow_correct t j x
        (by omega) (fun y hy => hrow y (by omega))
    have hlen' : (updRow (j + 1) t).length = n + 1 := by
      unfold updRow
      simp [ht]
    have hstep := ih (j + 1) (updRow (j + 1) t) hlen' hrow' m hm
    have hshift : (j + 1) + k = j + (k + 1) := by omega
    rwa [hshift] at hstep

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
    rw [List.foldl_map]
    exact msum_congr _ (fun j _ => ih (m - j * (k + 1)))

theorem impl_correct : ∀ n, impl n = partitionSpec n := by
  intro n
  unfold impl partitionSpec
  have hin : (initTable n).length = n + 1 := by
    simp [initTable]
  have hcalc := tableItFrom_correct n 0 n (initTable n) hin
    (fun x hx => initTable_getD n x hx) n (Nat.lt_succ_self n)
  have hget : (tableItFrom 0 n (initTable n)).getD n 0 = rows n n := by
    rwa [Nat.zero_add] at hcalc
  rw [hget]
  exact rows_eq_partAux n n

end Submission
