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

/-- The sizes `k, k-1, …, 1`, in the order `itAdd` applies them. -/
def succRange : Nat → List Nat
  | 0 => []
  | k + 1 => (k + 1) :: succRange k

theorem succRange_succ (k : Nat) :
    succRange (k + 1) = (k + 1) :: succRange k := rfl

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

/-- `succRange (k+1)` is `k+1` in front of `succRange k`, and the same list
written in the other order. Only the front-cons form is ever used. -/
theorem succRange_cons (k : Nat) :
    (k + 1) :: succRange k = succRange (k + 1) := succRange_succ k

/-- `succRange (k+1)` is the size-`k+1` step in front of the smaller ones.
This is definitional, and it is the form `coin` peels with `coin_cons`. -/
theorem coin_succRange (k : Nat) (f : Nat → Nat) :
    ∀ m, coin (succRange (k + 1)) f m = T (k + 1) (coin (succRange k) f) m := by
  intro m
  rw [succRange_succ, coin_cons]

/-- Every size in `succRange k` is positive: the list holds `k, k-1, …, 1`,
all successors. -/
theorem succRange_pos (k : Nat) : ∀ y ∈ succRange k, 0 < y := by
  induction k with
  | zero =>
    intro y hy
    cases hy
  | succ k ih =>
    intro y hy
    rw [succRange_succ, List.mem_cons] at hy
    rcases hy with h | hy
    · have hpos : 0 < k + 1 := Nat.succ_pos k
      rw [h]
      exact hpos
    · exact ih y hy

/-- A step of size `x` applied *after* the steps in `ds` is the same operator
as that step applied *before* them — the two differ only in where the step sits
in the list. This is the pointwise form of the commutation in `Coin.lean`, and
it is what lets a step be moved to the front of the list. -/
theorem coin_step (ds : List Nat) (x : Nat) (f : Nat → Nat) :
    ∀ m, coin ds (T x f) m = coin (ds ++ [x]) f m := by
  induction ds with
  | nil =>
    intro m
    rfl
  | cons d ds ih =>
    intro m
    rw [coin_cons, List.cons_append]
    -- both sides are `T d` applied at column `m`, and the IH says the two
    -- arguments agree at *every* column, so they agree as functions
    have h := ih
    have hfun : coin ds (T x f) = coin (ds ++ [x]) f := by
      funext c
      exact h c
    rw [hfun, coin_cons]

/-- `coin ds f` only ever reads `f` at columns *at or below* its own argument:
the head sums `f (c - j*d)` over `j`, and each such index is `≤ c`; the tail is
read at `c` itself. So agreement on columns `< n` propagates through `coin` on
columns `< n`.

This is the reason the whole proof can be stated on column-reading functions
instead of on lists: nothing downstream ever looks at a column above the one
it was asked about, so the list's length only has to cover the queried column. -/
theorem coin_congr (ds : List Nat) {f g : Nat → Nat} {n : Nat}
    (h : ∀ c, c < n → f c = g c) :
    ∀ c, c < n → coin ds f c = coin ds g c := by
  induction ds with
  | nil =>
    intro c hc
    exact h c hc
  | cons d ds ih =>
    intro c hc
    rw [coin_cons]
    unfold T
    refine msum_congr _ ?_
    intro j _
    have hle : c - j * d ≤ c := Nat.sub_le _ _
    have hlt : c - j * d < n := by omega
    exact ih (c - j * d) hlt

/-- `itAdd k t` applies the row steps of sizes `k, k-1, …, 1`, and `coin`
applied to that list computes the same column-reading function.

The statement is pointwise and bounded by `m < t.length`. That is not a
restriction: `nthNat` reads 0 past the end, but `T` does not, so the two
functions genuinely differ outside the range and only agree inside it. -/
theorem itAdd_coin (k : Nat) (t : List Nat) (m : Nat) (hm : m < t.length) :
    Submission.nthNat (Submission.itAdd k t) m
      = coin (succRange k) (Submission.nthNat t) m := by
  induction k generalizing t with
  | zero =>
    rfl
  | succ k ih =>
    -- `itAdd (k+1) t = itAdd k (updRowAdd (k+1) t)`, and the step preserves the
    -- length, so the queried column stays in range for the k remaining steps
    have hlen : m < (Submission.updRowAdd (k + 1) t).length := by
      rw [Probe2.length_updRowAdd (k + 1) t (Nat.succ_pos k)]
      exact hm
    rw [Submission.itAdd, ih _ hlen]
    -- substitute the stepped table's column function with `T (k+1)` of the
    -- original; `coin_congr` propagates the pointwise equality through `coin`,
    -- which only ever reads columns at or below the one it is asked for
    have hcol : ∀ c, c < t.length →
        Submission.nthNat (Submission.updRowAdd (k + 1) t) c
          = T (k + 1) (Submission.nthNat t) c := by
      intro c hc
      have hmsum := nthNat_updRowAdd_eq_msum (k + 1) (Nat.succ_pos k) t c hc
      show Submission.nthNat (Submission.updRowAdd (k + 1) t) c
        = T (k + 1) (Submission.nthNat t) c
      unfold T
      exact hmsum
    rw [succRange_succ, coin_cons]
    rw [coin_congr (succRange k) hcol m hm]
    -- move the size-(k+1) step to the front of the list: the operator is
    -- unchanged, and `coin_append` then peels it off. This is the commutation
    -- result from `Coin.lean`, and it is the one place where the
    -- implementation's decreasing iteration order is reconciled with the
    -- spec's increasing recurrence.
    rw [coin_step]
    exact (coin_append (succRange k) (succRange_pos k) (k + 1) (Nat.succ_pos k)
      (Submission.nthNat t)) m

/-- A row step of size `d` on the table is, on the column-reading function,
exactly the operator `T d`. This is the pointwise form of
`nthNat_updRowAdd_eq_msum`, and it is what lets the invariant be stated on
functions instead of on lists. -/
theorem nthNat_updRowAdd_T (d : Nat) (hd : 0 < d) (t : List Nat) (m : Nat)
    (hm : m < t.length) :
    Submission.nthNat (Submission.updRowAdd d t) m
      = T d (Submission.nthNat t) m :=
  nthNat_updRowAdd_eq_msum d hd t m hm
/-- Iterating the invariant over the whole size list: if the table satisfies
`Inv k` then applying the row step of size `k+1` gives `Inv (k+1)`. The list
`succRange (k+1)` puts that step in front, so `coin_congr` and `coin_cons`
chain the steps in increasing order — the order `inv_step` needs. -/
theorem inv_coin (n : Nat) (len : Nat) (f : Nat → Nat) (h : Inv 0 len f) :
    Inv n len (coin (succRange n) f) := by
  induction n with
  | zero =>
    -- no steps: the table is unchanged, and the base invariant is exactly Inv 0
    intro m hm
    exact h m hm
  | succ n ih =>
    -- `coin (succRange (n+1)) f = T (n+1) (coin (succRange n)) f`; apply the
    -- inductive hypothesis to get `Inv n` on the inner composition, then one
    -- `inv_step` to advance it to `Inv (n+1)`.
    -- `len` and `f` are fixed, so the induction on `n` leaves both untouched
    have hinner : Inv n len (coin (succRange n) f) := ih
    have hcol : (fun m => coin (succRange (n + 1)) f m)
        = T (n + 1) (coin (succRange n) f) := by
      funext m
      exact coin_succRange n f m
    have hfinal := inv_step n len (coin (succRange n) f) hinner
    -- rewrite the column function from `T (n+1) ∘ coin` to `coin (succRange (n+1))`
    intro m hm
    have := hfinal m hm
    rwa [← hcol] at this
/-- The implementation computes `p(n)` for every `n`.

Three facts are chained:
  * `inv_init` puts the initial table in the `Inv 0` regime;
  * `inv_coin` carries that through all `n` row steps to `Inv n`, so column
    `m` reads `partAux n m` — the spec's value;
  * `itAdd_coin` identifies the actual streaming loop with `coin (succRange n)`.

The column read is `n`, and `initTable n` has length `n + 1`, so `n` is in
range. The result is `partAux n n`, which is `partitionSpec n`. -/
theorem impl_correct (n : Nat) :
    Submission.impl n = partitionSpec n := by
  unfold Submission.impl partitionSpec
  -- the initial table is in the `Inv 0` regime
  have h0 := inv_init n
  -- after all n row steps, the column function reads `partAux n`
  have hn := inv_coin n (Submission.initTable n).length
    (Submission.nthNat (Submission.initTable n)) h0
  -- the streaming loop computes that same column function
  have hit := itAdd_coin n (Submission.initTable n) n (by
    simp [Submission.initTable])
  -- column `n` is in range (the table has length `n + 1`) and is not `0`
  have hlen : n < (Submission.initTable n).length := by
    simp [Submission.initTable]
  have hcol := hn n hlen
  rw [hit, hcol]
  -- column `n` is never column `0` (except at n = 0, where `partAux 0 0 = 1`
  -- anyway), so the `if` collapses to `partAux n n`
  split
  · rename_i h
    subst h
    exact partAux_zero 0 |>.symm
  · rfl

end Probe
