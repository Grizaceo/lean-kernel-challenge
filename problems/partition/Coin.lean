import Spec
import Submission
import Msum

namespace Probe

/-! ## The row-step operator, and why its order does not matter -/

/-- The `d`-step row operator: sum the column over multiplicities of part size
`d`. This is `updRowAdd` read column-wise. -/
def T (d : Nat) (f : Nat → Nat) : Nat → Nat :=
  fun m => msum (fun j => f (m - j * d)) (m / d + 1)

/-- A `msum` whose summands all vanish is zero. -/
theorem msum_zeros {f : Nat → Nat} {M : Nat} (h : ∀ j, j < M → f j = 0) :
    msum f M = 0 := by
  induction M with
  | zero => rfl
  | succ M ih =>
    rw [msum_succ, h M (Nat.lt_succ_self M),
      ih (fun j hj => h j (Nat.lt_trans hj (Nat.lt_succ_self M))), Nat.add_zero]

/-- `msum` distributes over addition of the summands. -/
theorem msum_add {f g : Nat → Nat} :
    ∀ (M : Nat), msum (fun i => f i + g i) M = msum f M + msum g M := by
  intro M
  induction M with
  | zero => simp [msum_zero]
  | succ M ih =>
    rw [msum_succ, msum_succ, msum_succ, ih]
    ac_rfl

/-- Swapping the order of summation over a rectangular range. Both sides sum
`g i j` over all pairs `i < K`, `j < L`, so they agree; peeling the last `j`
off the left and the last `i` off the right makes this syntactically visible. -/
theorem msum_swap (g : Nat → Nat → Nat) :
    ∀ (K L : Nat), msum (fun i => msum (fun j => g i j) L) K
        = msum (fun j => msum (fun i => g i j) K) L := by
  intro K L
  induction L with
  | zero =>
    have hz : msum (fun i => msum (fun j => g i j) 0) K = 0 := by
      have h : ∀ i, i < K → msum (fun j => g i j) 0 = 0 := by
        intro i _
        exact msum_zero _
      exact msum_zeros h
    rw [hz, msum_zero]
  | succ L ih =>
    have hdist : msum (fun i => msum (fun j => g i j) (L + 1)) K
        = msum (fun i => msum (fun j => g i j) L) K
          + msum (fun i => g i L) K := by
      calc msum (fun i => msum (fun j => g i j) (L + 1)) K
          = msum (fun i => (msum (fun j => g i j) L + g i L)) K := by
            apply msum_congr K
            intro i _
            exact msum_succ (fun j => g i j) L
        _ = _ := msum_add K
    have hinner : msum (fun j => msum (fun i => g i j) K) L + msum (fun i => g i L) K
        = msum (fun j => msum (fun i => g i j) K) (L + 1) :=
      (msum_succ (fun j => msum (fun i => g i j) K) L).symm
    rw [hdist, ih, hinner]

/-- Widening a `msum` range: indices past `M` contribute nothing, provided they
contribute nothing on the target side. -/
theorem msum_extend {f g : Nat → Nat} {M M' : Nat} (hM : M ≤ M')
    (h1 : ∀ j, j < M → f j = g j) (h2 : ∀ j, M ≤ j → j < M' → g j = 0) :
    msum f M = msum g M' := by
  induction M' generalizing M with
  | zero =>
    have hM0 : M = 0 := by omega
    subst hM0
    simp [msum_zero]
  | succ M' ih =>
    by_cases hc : M ≤ M'
    · have hlast : g M' = 0 := h2 M' (by omega) (by omega)
      have key : msum f M = msum g M' :=
        ih hc h1 (fun j hM' hlt => h2 j hM' (by omega))
      rw [msum_succ, hlast, key, Nat.add_zero]
    · have hMeq : M = M' + 1 := by omega
      have hlast : f M' = g M' := h1 M' (by omega)
      have key : msum f M' = msum g M' := msum_congr M' (fun j hj => h1 j (by omega))
      rw [hMeq, msum_succ, key, msum_succ, hlast]

/-- The triangle double sum, written so that symmetry in `a`/`b` is visible:
the guard and the argument are both symmetric, and the ranges are the natural
ones. -/
def triSum (a b m : Nat) (f : Nat → Nat) : Nat :=
  msum (fun i => msum (fun j =>
      if i * a + j * b ≤ m then f (m - i * a - j * b) else 0) (m / b + 1)) (m / a + 1)

/-- Applying the `a`-step then the `b`-step is the triangle sum. The inner range
is widened from `(m - i*a)/b + 1` to `m/b + 1`; the extra indices are exactly
those the guard rejects, so they contribute zero. -/
theorem T_seq (a b m : Nat) (hb : 0 < b) (f : Nat → Nat) :
    T a (T b f) m = triSum a b m f := by
  unfold T
  apply msum_congr
  intro i _
  -- `i` ranges over `m/a + 1`, so `i*a ≤ m`
  have hi : i * a ≤ m := Nat.mul_le_of_le_div a i m (by omega)
  have key : msum (fun j => f ((m - i * a) - j * b)) ((m - i * a) / b + 1)
      = msum (fun j => f (m - i * a - j * b)) ((m - i * a) / b + 1) := by
    refine msum_congr _ (fun j _ => ?_)
    -- (m - i*a) - j*b = m - (i*a + j*b) = m - i*a - j*b
    have h := Nat.sub_sub m (i * a) (j * b)
    rw [h]
  rw [key]
  refine msum_extend (M := (m - i * a) / b + 1) (M' := m / b + 1) ?_ ?_ ?_
  · have hsub : m - i * a ≤ m := Nat.sub_le m (i * a)
    have h : (m - i * a) / b ≤ m / b := Nat.div_le_div_right (c := b) hsub
    omega
  · intro j hj
    -- j < (m - i*a)/b + 1  ⟹  j ≤ (m - i*a)/b  ⟹  j*b ≤ m - i*a
    have hjle : j ≤ (m - i * a) / b := by omega
    have hjle' : j * b ≤ m - i * a := Nat.mul_le_of_le_div b j (m - i * a) hjle
    -- i*a + j*b ≤ i*a + (m - i*a) = m
    have htotal : i * a + j * b ≤ m := by omega
    rw [if_pos htotal]
  · intro j hj1 hj2
    -- j > (m - i*a)/b  ⟹  m - i*a < j*b, and i*a ≤ m, so i*a + j*b > m
    have hgt : (m - i * a) / b < j := by omega
    have hlt : m - i * a < j * b :=
      (Nat.div_lt_iff_lt_mul (k := b) (x := m - i * a) (y := j) hb).mp hgt
    -- i*a + j*b > i*a + (m - i*a) = m
    have hneg : ¬ i * a + j * b ≤ m := by omega
    rw [if_neg hneg]

/-- The same double sum with both ranges widened to `m + 1`. The extra indices
are exactly those the guard rejects, so the value is unchanged. With equal
ranges, symmetry in `a`/`b` is visible in the summand alone. -/
def fullSum (a b m : Nat) (f : Nat → Nat) : Nat :=
  msum (fun i => msum (fun j =>
      if i * a + j * b ≤ m then f (m - i * a - j * b) else 0) (m + 1)) (m + 1)

/-- With equal ranges, the double sum is symmetric in the two part sizes.

The symmetry is the *diagonal* one: the summand is invariant under exchanging
`(a, i)` with `(b, j)` simultaneously, and `msum_swap` lets us make that exchange
in the indices. Note that exchanging `a` and `b` at a *fixed* pair `(i, j)` is
not a symmetry — only the simultaneous exchange is. -/
theorem fullSum_comm (a b m : Nat) (f : Nat → Nat) :
    fullSum a b m f = fullSum b a m f := by
  unfold fullSum
  -- exchange the summation order
  rw [msum_swap (g := fun i j =>
      if i * a + j * b ≤ m then f (m - i * a - j * b) else 0) (K := m + 1) (L := m + 1)]
  apply msum_congr
  intro j _
  apply msum_congr
  intro i _
  -- after the swap, the two guards are `i*a + j*b ≤ m` and `j*b + i*a ≤ m`,
  -- the same inequality written in the other order
  have e : i * a + j * b = j * b + i * a := Nat.add_comm _ _
  by_cases h : i * a + j * b ≤ m
  · have h' : j * b + i * a ≤ m := by rwa [e] at h
    rw [if_pos h, if_pos h']
    -- m - i*a - j*b = m - (i*a + j*b) = m - (j*b + i*a) = m - j*b - i*a
    have e1 := Nat.sub_sub m (i * a) (j * b)
    have e2 := Nat.sub_sub m (j * b) (i * a)
    rw [e1, e2, e]
  · have h' : ¬ j * b + i * a ≤ m := by rwa [e] at h
    rw [if_neg h, if_neg h']

/-- The natural ranges are truncations of the uniform ones: an outer index past
`m/a` has `i*a > m`, and an inner index past `m/b` has `j*b > m`, so the guard
rejects them.

Both part sizes must be positive. At `b = 0` the summand does not depend on `j`
at all, while the inner range grows from `m/0 + 1 = 1` to `m + 1`, so the
widening would scale the value rather than preserve it. -/
theorem triSum_full (a b m : Nat) (ha : 0 < a) (hb : 0 < b) (f : Nat → Nat) :
    triSum a b m f = fullSum a b m f := by
  unfold triSum fullSum
  refine msum_extend (M := m / a + 1) (M' := m + 1) ?_ ?_ ?_
  · have h : m / a ≤ m := Nat.div_le_self m a
    omega
  · intro i _
    show msum (fun j => if i * a + j * b ≤ m then f (m - i * a - j * b) else 0) (m / b + 1)
        = msum (fun j => if i * a + j * b ≤ m then f (m - i * a - j * b) else 0) (m + 1)
    refine msum_extend (M := m / b + 1) (M' := m + 1) ?_ ?_ ?_
    · have h : m / b ≤ m := Nat.div_le_self m b
      omega
    · intro j _
      rfl
    · intro j hj1 hj2
      -- j > m/b  ⟹  m < j*b, so the guard can never hold
      have hgt : m / b < j := by omega
      have hlt : m < j * b :=
        (Nat.div_lt_iff_lt_mul (k := b) (x := m) (y := j) hb).mp hgt
      rw [if_neg]
      omega
  · intro i hi1 hi2
    have hlt : m < i * a := by
      have h : m / a < i := by omega
      have h' := (Nat.div_lt_iff_lt_mul (k := a) (x := m) (y := i) ha).mp h
      omega
    have hz : ∀ j, j < m + 1 →
        (if i * a + j * b ≤ m then f (m - i * a - j * b) else 0) = 0 := by
      intro j _
      have hgt : m < i * a := hlt
      rw [if_neg]
      omega
    exact msum_zeros hz

/-- The triangle sum is symmetric in the two part sizes. -/
theorem triSum_comm (a b m : Nat) (ha : 0 < a) (hb : 0 < b) (f : Nat → Nat) :
    triSum a b m f = triSum b a m f := by
  rw [triSum_full a b m ha hb f, triSum_full b a m hb ha f, fullSum_comm]

/-- The two row-step operators commute. This is what lets `itAdd` apply the part
sizes in decreasing order and still compute the same table as the spec.

The positivity of both part sizes is essential, not cosmetic: for `d = 0` the
`d`-step scales the column and does not commute with a genuine step. -/
theorem T_comm (a b : Nat) (ha : 0 < a) (hb : 0 < b) (f : Nat → Nat) :
    T a (T b f) = T b (T a f) := by
  funext m
  rw [T_seq a b m hb f, triSum_comm a b m ha hb f, T_seq b a m ha f]

/-! ## Part sizes as a list, and its order-independence -/

/-- `coin ds f m` applies the row step for every part size in `ds`, in order. -/
def coin : List Nat → (Nat → Nat) → Nat → Nat
  | [], f, m => f m
  | d :: ds, f, m => T d (coin ds f) m

theorem coin_cons (d : Nat) (ds : List Nat) (f : Nat → Nat) (m : Nat) :
    coin (d :: ds) f m = T d (coin ds f) m := rfl

/-- A step at the end of the list can be pulled to the front, by commutation. -/
theorem coin_append (ds : List Nat) (hds : ∀ y ∈ ds, 0 < y) (x : Nat) (hx : 0 < x)
    (f : Nat → Nat) : ∀ (m : Nat), coin (ds ++ [x]) f m = T x (coin ds f) m := by
  intro m
  induction ds generalizing x m with
  | nil => rfl
  | cons d ds ih =>
    have hd : 0 < d := hds d (by simp)
    have hds' : ∀ y ∈ ds, 0 < y := fun y hy => hds y (by simp [hy])
    -- peel the head of `ds ++ [x]`
    show T d (coin (ds ++ [x]) f) m = T x (T d (coin ds f)) m
    -- ih is pointwise in the column index
    have hfun : coin (ds ++ [x]) f = T x (coin ds f) := funext (ih hds' x hx)
    show T d (coin (ds ++ [x]) f) m = T x (T d (coin ds f)) m
    rw [hfun]
    -- T_comm d x : T d (T x f) = T x (T d f), which is the goal
    exact congrArg (fun g => g m) (T_comm d x hd hx (coin ds f))

/-- `coin` does not depend on the order of the part sizes: a list and its
reverse give the same count. This is what lets `itAdd` walk the part sizes
downwards while still computing the spec's table. -/
theorem coin_reverse (ds : List Nat) (hds : ∀ y ∈ ds, 0 < y) (f : Nat → Nat) :
    ∀ (m : Nat), coin ds.reverse f m = coin ds f m := by
  intro m
  induction ds generalizing m with
  | nil => rfl
  | cons a ds ih =>
    have ha : 0 < a := hds a (by simp)
    have hds' : ∀ y ∈ ds, 0 < y := fun y hy => hds y (by simp [hy])
    have hrev : ∀ y ∈ ds.reverse, 0 < y := by
      intro y hy
      rw [List.mem_reverse] at hy
      exact hds' y hy
    show coin (a :: ds).reverse f m = coin (a :: ds) f m
    rw [List.reverse_cons, coin_append ds.reverse hrev a ha f]
    show T a (coin ds.reverse f) m = T a (coin ds f) m
    unfold T
    apply msum_congr
    intro k _
    exact ih hds' (m - k * a)

end Probe
