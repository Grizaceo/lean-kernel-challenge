import Spec

/-! # permanent — DFS over only the three ones per row.

## The baseline

The Spec's `permanentRows` walks **every column** of the width:

```
permanentRows (row :: rows) used =
  (List.range width).foldl (fun total j =>
    let entry := row.getD j 0
    if entry = 0 || used.testBit j then total
    else total + entry * permanentRows width rows (used ||| (1 <<< j))) 0
```

so per node of the search tree it pays an O(width) scan, and each `row.getD j 0`
walks a linked list from the front. With `width = 16` that is 16 list steps per
node where **3** would do, and the matrix is materialised as
`List (List Nat)` — 16 rows of 16 boxed `Nat`s.

Measured on the judge's own inputs (playground run 273): 306M / 9.36B /
131.7B instructions at dimension 6 / 12 / 16, with **5.1 GB peak memory** at
dimension 16. That memory figure is the tell: it is allocation cost, not search
cost. Rank 1 sits at 143,736,178.

## The idea

The Spec fixes the branching factor at exactly three: "the diagonal and two
seeded off-diagonal columns". `permanentEntry` returns `1` only at the diagonal,
at `permanentColumnOne`, and at `permanentColumnTwo`; every other entry is a
literal `0`. So branching on all 16 columns tests 13 entries whose answer is
already determined.

**Generate the three candidate columns arithmetically at each node and never
materialise a row, a matrix, or a permutation list.** Each node then costs three
column generations instead of sixteen list steps, and allocates nothing at all.

The branch weight is kept as the Spec's own `permanentEntry dimension seed i c`
rather than folded to `1`, so the recursion stays faithful to the spec's
definition and not merely to my reading of it.

## The two branches

`permanentEntry` is `1` everywhere when `dimension < 3` — the Spec uses the full
square matrix there — but `permanentColumnOne`/`Two` are only meaningful from
dimension 3 up. The Spec's three judge inputs are dimension 6 / 12 / 16, yet
faithfulness means handling the small case too, so `impl` dispatches:
`fullAux` enumerates every column when `dimension < 3` (cheap, since there are at
most 2 rows) and `sparseAux` enumerates the three seeded columns otherwise.

## Cost

Nodes are 3^d over `d = dimension` levels, so ≈ 3^16 ≈ 43M leaves. The
*effective* branching is unchanged from the baseline, but the per-node constant
drops by roughly 16/3 and the allocation goes to zero. That is the whole claim:
**same search, cheaper node, no memory pressure.** The 5.1 GB baseline peak is
what this removes.

The input is decoded exactly as the Spec does — `n >>> 32` for the dimension,
`n &&& 0xffffffff` for the seed — so the same packed input yields the same
matrix.

## Proof status

`impl_correct` is proved. What follows is a full kernel proof that
`impl n = permanentSpecN n` for every packed input, in `Init` alone: no Mathlib,
no `sorry`, no `native_decide`, and `decide` only on closed terms. The audit is
the problem's own whitelist — `#print axioms impl_correct` reports
`[propext, Quot.sound]`, a subset of `permitted_axioms` in
`evaluation/problems/permanent/config.json`.

The two branches are argued separately. For `dimension < 3` the whole computation
is closed and evaluates: `d = 0` is the empty sum, `d = 1` a single 1, `d = 2` the
2x2 all-ones permanent, 2. For `3 ≤ dimension` the Spec's `O(width)` row scan is
replaced by three fold lemmas proved here by induction on the width, `foldl_zero`,
`foldl_two` and `foldl_three`: a sum over `List.range d` in which only zero, one
or two — respectively three — indices carry a nonzero weight equals that weight,
resp. the corresponding sum of those weights. `permanentEntry` is 1 at the
diagonal and at the two seeded columns and 0 everywhere else, so the three-index
lemma applied to exactly those three indices evaluates the Spec's row scan, and
induction on the row count finishes the branch.
-/

namespace Submission

-- Row traversal for `dimension < 3`: every entry of every row is 1, so the inner
-- loop must try *all* `dimension` columns, not just the diagonal neighbours — in a
-- 2x2 all-ones matrix row 0 can take column 1.
--
-- Rows are visited in the Spec's own order, ascending from 0. That order is not
-- cosmetic: `permanentColumnOne/Two` depend on the row index, so permuting the
-- row order changes which columns each row may use and changes the count — on the
-- judge's own 6x6 input a descending traversal returns 23 where the Spec returns 8.
mutual

/-- Result for rows `i .. dimension - 1` given `used`, where `rem` is the number
of rows still to serve. Row order is the Spec's, ascending from 0.

The order is not cosmetic. `permanentColumnOne/Two` depend on the row index, so
permuting the row order changes which columns each row may use and changes the
count: on the judge's own 6x6 input a descending traversal returns 23 where the
Spec returns 8. -/
def step : Nat → Nat → Nat → Nat → Nat → Nat
  | _, _, _, _, 0 => 1
  | dimension, seed, i, used, rem + 1 =>
    colSum dimension seed i used rem dimension

/-- Inner loop of `step`: every column of row `i`, from `left` down, so the
column index `dimension - left - 1` walks 0, 1, 2, …

`dimension < 3` case: every entry of every row is 1, so this must try *all*
`dimension` columns, not just the diagonal neighbours — in a 2x2 all-ones matrix
row 0 can take column 1. -/
def colSum : Nat → Nat → Nat → Nat → Nat → Nat → Nat
  | _, _, _, _, _, 0 => 0
  | dimension, seed, i, used, rem, left + 1 =>
    let c := dimension - left - 1
    let here :=
      if !used.testBit c then
        permanentEntry dimension seed i c
          * step dimension seed (i + 1) (used ||| (1 <<< c)) rem
      else 0
    here + colSum dimension seed i used rem left

/-- `3 ≤ dimension` case: each row has exactly three ones, at the diagonal and
at the two seeded off-diagonal columns, so only those three are tried. Row order
is the Spec's, 0 first — see `step`.

`rem` counts the rows still to serve, and the match is on `rem + 1`, so the
`rem` in the body is the *decremented* count: the row to serve is
`dimension - rem - 1`. Writing `dimension - rem` instead silently starts at row
1, which drops row 0 and never constrains the last row — on the judge's 6x6
input that returns 33 where the Spec returns 8. -/
def sparseAux : Nat → Nat → Nat → Nat → Nat
  | _, _, _, 0 => 1
  | dimension, seed, used, rem + 1 =>
    let i := dimension - rem - 1
    let c1 := permanentColumnOne dimension seed i
    let c2 := permanentColumnTwo dimension seed i
    let go (c : Nat) : Nat :=
      if used.testBit c then 0
      else permanentEntry dimension seed i c
        * sparseAux dimension seed (used ||| (1 <<< c)) rem
    go i + go c1 + go c2

end

/-- Sum over injective column choices for the rows still to serve. `dimension <
3`: every entry is 1, so scan all columns. -/
def fullAux (dimension seed used rem : Nat) : Nat :=
  step dimension seed (dimension - rem) used rem

/-- The mathematical permanent of the matrix selected by the packed input. -/
def impl (n : Nat) : Nat :=
  let d := permanentDimension n
  if d < 3 then fullAux d (permanentSeed n) 0 d
  else sparseAux d (permanentSeed n) 0 d

/-! ## Infrastructure

Only `Init` is available — no Mathlib. Everything below is proved from
scratch, so the fold lemmas are stated and proven here. -/

section Infra

theorem if_add (b : Bool) (t x : Nat) :
    (if b then t else t + x) = t + (if b then 0 else x) := by
  cases b <;> rfl

theorem foldl_congr_of (d : Nat) (g h : Nat → Nat → Nat) :
    ∀ (l : List Nat) (init : Nat),
      (∀ j, j ∈ l → j < d) →
      (∀ t j, j < d → g t j = h t j) →
      l.foldl g init = l.foldl h init := by
  intro l
  induction l with
  | nil => intro init _ _; rfl
  | cons a t ih =>
    intro init hl hc
    have ha : a < d := by have := hl a (by simp); exact this
    rw [List.foldl_cons, List.foldl_cons, hc _ a ha,
      ih _ (fun j hj => by have := hl j (by simp [hj]); exact this)
        (fun t j hj => hc t j hj)]

theorem mem_range_lt (d j : Nat) (h : j ∈ List.range d) : j < d := by
  simpa using h

theorem range_foldl_succ (f : Nat → Nat) (d : Nat) :
    (List.range (d + 1)).foldl (fun t j => t + f j) 0
      = (List.range d).foldl (fun t j => t + f j) 0 + f d := by
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- `getD` on a mapped range. -/
theorem map_range_getD : ∀ (d : Nat) (f : Nat → Nat) (j : Nat), j < d →
    ((List.range d).map f).getD j 0 = f j := by
  intro d
  induction d with
  | zero => intro f j hj; omega
  | succ d ih =>
    intro f j hj
    simp only [List.range_succ_eq_map, List.map_map, List.map_cons]
    cases j with
    | zero => rfl
    | succ j =>
      have h := ih (f ∘ Nat.succ) j (by omega)
      simp only [List.getD_cons_succ] at ⊢
      rw [h]
      rfl

end Infra

section Columns

theorem col_one_lt (d s i : Nat) (h3 : 3 ≤ d) : permanentColumnOne d s i < d := by
  unfold permanentColumnOne permanentSkipOne
  have hk : permanentMix32 (s ^^^ (i * 0x9e3779b9) ^^^ 0x85ebca6b) % (d - 1) < d - 1 :=
    Nat.mod_lt _ (by omega)
  split <;> omega

theorem col_one_ne (d s i : Nat) : permanentColumnOne d s i ≠ i := by
  unfold permanentColumnOne permanentSkipOne
  split <;> omega

theorem col_two_lt (d s i : Nat) (h3 : 3 ≤ d) : permanentColumnTwo d s i < d := by
  have h1 := col_one_lt d s i h3
  have h2 := col_one_ne d s i
  unfold permanentColumnTwo permanentSkipTwo permanentColumnOne permanentSkipOne
  have hk : permanentMix32 (s ^^^ (i * 0x9e3779b9) ^^^ 0xc2b2ae35) % (d - 2) < d - 2 :=
    Nat.mod_lt _ (by omega)
  simp only [Nat.min_def, Nat.max_def]
  split <;> split <;> split <;> split <;> omega

theorem col_two_ne_i (d s i : Nat) (h3 : 3 ≤ d) : permanentColumnTwo d s i ≠ i := by
  have h1 := col_one_lt d s i h3
  have h2 := col_one_ne d s i
  unfold permanentColumnTwo permanentSkipTwo permanentColumnOne permanentSkipOne
  have hk : permanentMix32 (s ^^^ (i * 0x9e3779b9) ^^^ 0xc2b2ae35) % (d - 2) < d - 2 :=
    Nat.mod_lt _ (by omega)
  simp only [Nat.min_def, Nat.max_def]
  split <;> split <;> split <;> split <;> omega

theorem col_two_ne_one (d s i : Nat) (h3 : 3 ≤ d) :
    permanentColumnTwo d s i ≠ permanentColumnOne d s i := by
  have h1 := col_one_lt d s i h3
  have h2 := col_one_ne d s i
  unfold permanentColumnTwo permanentSkipTwo permanentColumnOne permanentSkipOne
  have hk : permanentMix32 (s ^^^ (i * 0x9e3779b9) ^^^ 0xc2b2ae35) % (d - 2) < d - 2 :=
    Nat.mod_lt _ (by omega)
  simp only [Nat.min_def, Nat.max_def]
  split <;> split <;> split <;> split <;> omega

/-- At one of the three distinguished columns the entry is 1. -/
theorem entry_pos (d s i j : Nat) (h3 : 3 ≤ d)
    (h : i = j ∨ j = permanentColumnOne d s i ∨ j = permanentColumnTwo d s i) :
    permanentEntry d s i j = 1 := by
  have hne : ¬ (d < 3) := by omega
  simp only [permanentEntry, if_neg hne]
  cases h with
  | inl h => simp [h]
  | inr h =>
    cases h with
    | inl h => simp [h]
    | inr h => simp [h]

/-- Off the three distinguished columns the entry is 0. -/
theorem entry_neg (d s i j : Nat) (h3 : 3 ≤ d)
    (h : ¬ (i = j ∨ j = permanentColumnOne d s i ∨ j = permanentColumnTwo d s i)) :
    permanentEntry d s i j = 0 := by
  have hne : ¬ (d < 3) := by omega
  have h1 : ¬ i = j := fun hj => h (Or.inl hj)
  have h2 : ¬ j = permanentColumnOne d s i := fun hj => h (Or.inr (Or.inl hj))
  have h4 : ¬ j = permanentColumnTwo d s i := fun hj => h (Or.inr (Or.inr hj))
  simp [permanentEntry, hne, h1, h2, h4]

end Columns

section Sums

/-- All weights vanish. -/
theorem foldl_zero (f : Nat → Nat) : ∀ (d : Nat),
    (∀ j, j < d → f j = 0) →
      (List.range d).foldl (fun t j => t + f j) 0 = 0 := by
  intro d
  induction d with
  | zero => intro _; rfl
  | succ d ih =>
    intro hz
    rw [range_foldl_succ f d, ih (fun j hj => hz j (by omega)), hz d (by omega),
      Nat.add_zero]

/-- Exactly one weight survives. -/
theorem foldl_one (f : Nat → Nat) : ∀ (d : Nat),
    (∀ a, a < d → (∀ j, j < d → j ≠ a → f j = 0) →
      (List.range d).foldl (fun t j => t + f j) 0 = f a) := by
  intro d
  induction d with
  | zero => intro a ha; omega
  | succ d ih =>
    intro a ha hz
    by_cases hd : d = a
    · have h0 := foldl_zero f d (fun j hj => hz j (by omega) (by omega))
      rw [range_foldl_succ f d, h0, hd]
      omega
    · have hrec := ih a (by omega) (fun j hj hja => hz j (by omega) hja)
      rw [range_foldl_succ f d, hrec, hz d (by omega) hd, Nat.add_zero]

/-- Exactly two weights survive. -/
theorem foldl_two (f : Nat → Nat) : ∀ (d : Nat),
    (∀ a b, a < d → b < d → a ≠ b → (∀ j, j < d → j ≠ a → j ≠ b → f j = 0) →
      (List.range d).foldl (fun t j => t + f j) 0 = f a + f b) := by
  intro d
  induction d with
  | zero => intro a b ha; omega
  | succ d ih =>
    intro a b ha hb hab hz
    by_cases hda : d = a
    · have hrec := foldl_one f d b (by omega) (fun j hj hjb => hz j (by omega) (by omega) hjb)
      rw [range_foldl_succ f d, hrec, hda]
      omega
    · by_cases hdb : d = b
      · have hrec := foldl_one f d a (by omega) (fun j hj hja => hz j (by omega) hja (by omega))
        rw [range_foldl_succ f d, hrec, hdb]
      · have hrec := ih a b (by omega) (by omega) (by omega)
          (fun j hj hja hjb => hz j (by omega) hja hjb)
        rw [range_foldl_succ f d, hrec, hz d (by omega) hda hdb, Nat.add_zero]

/-- Exactly three weights survive, in any order. -/
theorem foldl_three (f : Nat → Nat) : ∀ (d : Nat),
    (∀ a b c, a < d → b < d → c < d → a ≠ b → a ≠ c → b ≠ c →
      (∀ j, j < d → j ≠ a → j ≠ b → j ≠ c → f j = 0) →
      (List.range d).foldl (fun t j => t + f j) 0 = (f a + f b) + f c) := by
  intro d
  induction d with
  | zero => intro a b c ha; omega
  | succ d ih =>
    intro a b c ha hb hc hab hac hbc hz
    by_cases hda : d = a
    · have hrec := foldl_two f d b c (by omega) (by omega) (by omega)
          (fun j hj hjb hjc => hz j (by omega) (by omega) hjb hjc)
      rw [range_foldl_succ f d, hrec, hda]
      omega
    · by_cases hdb : d = b
      · have hrec := foldl_two f d a c (by omega) (by omega) (by omega)
            (fun j hj hja hjc => hz j (by omega) hja (by omega) hjc)
        rw [range_foldl_succ f d, hrec, hdb]
        omega
      · by_cases hdc : d = c
        · have hrec := foldl_two f d a b (by omega) (by omega) (by omega)
              (fun j hj hja hjb => hz j (by omega) hja hjb (by omega))
          rw [range_foldl_succ f d, hrec, hdc]
        · have hrec := ih a b c (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
              (fun j hj hja hjb hjc => hz j (by omega) hja hjb hjc)
          rw [range_foldl_succ f d, hrec, hz d (by omega) hda hdb hdc, Nat.add_zero]

end Sums

section Rows

/-- The rows from index `k` on, indexed explicitly. -/
def rowsFrom (d s k : Nat) : List (List Nat) :=
  (List.range (d - k)).map (fun j => genPermanentRow d s (k + j))

theorem rowsFrom_zero (d s : Nat) : rowsFrom d s 0 = genPermanentMatrix d s := by
  simp [rowsFrom, genPermanentMatrix, genPermanentRow, Nat.zero_add]

theorem range_map_succ (g : Nat → List Nat) (n : Nat) :
    ((List.range (n + 1)).map g)
      = g 0 :: ((List.range n).map (fun j => g (j + 1))) := by
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  rfl

theorem rowsFrom_cons (d s k : Nat) (hk : k < d) :
    rowsFrom d s k = genPermanentRow d s k :: rowsFrom d s (k + 1) := by
  have h1 : d - k = (d - k - 1) + 1 := by omega
  have hidx : d - (k + 1) = d - k - 1 := by omega
  unfold rowsFrom
  rw [h1, hidx, range_map_succ, Nat.add_zero]
  congr 1
  apply List.map_congr_left
  intro a ha
  congr 1
  omega

theorem row_getD (d s i j : Nat) (h : j < d) :
    (genPermanentRow d s i).getD j 0 = permanentEntry d s i j :=
  map_range_getD d (permanentEntry d s i) j h

theorem matrix_length (d s : Nat) : (genPermanentMatrix d s).length = d := by
  simp [genPermanentMatrix, List.length_map, List.length_range]

theorem spec_of_rows (d s : Nat) :
    permanentSpec (genPermanentMatrix d s) = permanentRows d (genPermanentMatrix d s) 0 := by
  show permanentRows (genPermanentMatrix d s).length (genPermanentMatrix d s) 0 = _
  rw [matrix_length]

end Rows

/-! ## The `3 ≤ dimension` branch

The Spec scans all `dimension` columns of a row. Off the diagonal and the two
seeded columns the entry is 0, so the scan adds nothing there. -/

/-- The Spec's row scan, rewritten as a sum over the surviving weights. -/
theorem foldl_rows (d : Nat) (g : Nat → Nat) (tail : Nat → Nat) (used : Nat)
    (row : List Nat) (init : Nat) :
    (∀ j, j < d → row.getD j 0 = g j) →
    (List.range d).foldl (fun total j =>
        let entry := row.getD j 0
        if decide (entry = 0) || used.testBit j then total
        else total + entry * tail j) init
      = (List.range d).foldl (fun t j =>
          t + (if decide (g j = 0) || used.testBit j then 0 else g j * tail j)) init := by
  intro hl
  refine foldl_congr_of d _ _ (List.range d) init (mem_range_lt d) ?_
  intro total j hj
  have hgj : row.getD j 0 = g j := hl j hj
  simp only [hgj]
  exact if_add _ _ _

theorem spec_sparse (d s : Nat) (h3 : 3 ≤ d) :
    ∀ (n : Nat), n ≤ d → ∀ (used : Nat),
      permanentRows d (rowsFrom d s (d - n)) used = sparseAux d s used n := by
  intro n
  induction n with
  | zero =>
    intro _ used
    have hnil : rowsFrom d s (d - 0) = [] := by simp [rowsFrom]
    rw [hnil]
    show permanentRows d [] used = 1
    rfl
  | succ n ih =>
    intro hn used
    have hn' : n ≤ d := by omega
    have hsub : d - (n + 1) = d - n - 1 := by omega
    have hlt : d - n - 1 < d := by omega
    have hsub1 : d - n - 1 + 1 = d - n := Nat.sub_add_cancel (by omega)
    have hrow : rowsFrom d s (d - n - 1)
        = genPermanentRow d s (d - n - 1) :: rowsFrom d s (d - n) :=
      calc rowsFrom d s (d - n - 1)
          = genPermanentRow d s (d - n - 1) :: rowsFrom d s (d - n - 1 + 1) :=
            rowsFrom_cons d s (d - n - 1) hlt
        _ = genPermanentRow d s (d - n - 1) :: rowsFrom d s (d - n) := by
          rw [hsub1]
    rw [hsub, hrow, permanentRows]
    have hih : ∀ u, permanentRows d (rowsFrom d s (d - n)) u = sparseAux d s u n := ih hn'
    simp only [hih]
    have hget : ∀ j, j < d →
        (genPermanentRow d s (d - n - 1)).getD j 0 = permanentEntry d s (d - n - 1) j :=
      fun j hj => row_getD d s (d - n - 1) j hj
    have hstep := foldl_rows d (permanentEntry d s (d - n - 1))
      (fun j => sparseAux d s (used ||| (1 <<< j)) n) used
      (genPermanentRow d s (d - n - 1)) 0 hget
    rw [hstep]
    have hz : ∀ j, j < d → j ≠ d - n - 1 → j ≠ permanentColumnOne d s (d - n - 1) →
        j ≠ permanentColumnTwo d s (d - n - 1) →
        (if decide (permanentEntry d s (d - n - 1) j = 0) || used.testBit j then 0
          else permanentEntry d s (d - n - 1) j
            * sparseAux d s (used ||| (1 <<< j)) n) = 0 := by
      intro j hj hji hjc1 hjc2
      have he := entry_neg d s (d - n - 1) j h3
        (by intro hc
            cases hc with
            | inl hc => exact hji hc.symm
            | inr hc =>
              cases hc with
              | inl hc => exact hjc1 hc
              | inr hc => exact hjc2 hc)
      have hb : (decide (permanentEntry d s (d - n - 1) j = 0) || used.testBit j) = true := by
        simp [he]
      simp [hb]
    have hsum := foldl_three
      (fun j => if decide (permanentEntry d s (d - n - 1) j = 0) || used.testBit j then 0
        else permanentEntry d s (d - n - 1) j * sparseAux d s (used ||| (1 <<< j)) n)
      d (d - n - 1) (permanentColumnOne d s (d - n - 1)) (permanentColumnTwo d s (d - n - 1))
      (by omega) (col_one_lt d s (d - n - 1) h3) (col_two_lt d s (d - n - 1) h3)
      (col_one_ne d s (d - n - 1)).symm
      (col_two_ne_i d s (d - n - 1) h3).symm
      (col_two_ne_one d s (d - n - 1) h3).symm hz
    rw [hsum]
    have e0 : permanentEntry d s (d - n - 1) (d - n - 1) = 1 :=
      entry_pos d s (d - n - 1) (d - n - 1) h3 (Or.inl rfl)
    have e1 : permanentEntry d s (d - n - 1) (permanentColumnOne d s (d - n - 1)) = 1 :=
      entry_pos d s (d - n - 1) (permanentColumnOne d s (d - n - 1)) h3
        (Or.inr (Or.inl rfl))
    have e2 : permanentEntry d s (d - n - 1) (permanentColumnTwo d s (d - n - 1)) = 1 :=
      entry_pos d s (d - n - 1) (permanentColumnTwo d s (d - n - 1)) h3
        (Or.inr (Or.inr rfl))
    simp [sparseAux, e0, e1, e2]

/-! ## The `dimension < 3` branch

`d < 3` means `d ∈ {0, 1, 2}`, so the whole computation is closed and
evaluates: the empty sum, the 1x1 case and the 2x2 all-ones case. -/

theorem entry_one_lt3 (d s i j : Nat) (h2 : d < 3) :
    permanentEntry d s i j = 1 := by
  simp only [permanentEntry, if_pos h2]

theorem spec_small (d s : Nat) (h2 : d < 3) :
    fullAux d s 0 d = permanentSpec (genPermanentMatrix d s) := by
  have hd : d = 0 ∨ d = 1 ∨ d = 2 := by omega
  rcases hd with rfl | rfl | rfl
  · rw [fullAux, step]
    simp [permanentSpec, permanentRows, genPermanentMatrix]
  · have he : ∀ (i j : Nat), permanentEntry 1 s i j = 1 := by
      intro i j
      exact entry_one_lt3 1 s i j (by omega)
    simp [fullAux, step, colSum, he, Nat.testBit]
    simp [permanentSpec, permanentRows, genPermanentMatrix, genPermanentRow, permanentEntry]
  · have he : ∀ (i j : Nat), permanentEntry 2 s i j = 1 := by
      intro i j
      exact entry_one_lt3 2 s i j (by omega)
    simp [fullAux, step, colSum, he, Nat.testBit]
    have key : genPermanentMatrix 2 s = (List.range 2).map (fun _ => [1, 1]) := by
      show (List.range 2).map (genPermanentRow 2 s) = (List.range 2).map (fun _ => [1, 1])
      refine List.map_congr_left ?_
      intro a ha
      have hr : genPermanentRow 2 s a = (List.range 2).map (fun _ => 1) := by
        show (List.range 2).map (permanentEntry 2 s a) = (List.range 2).map (fun _ => 1)
        refine List.map_congr_left ?_
        intro b hb
        exact he a b
      rw [hr]
      decide
    rw [key]
    decide

/-! ## The candidate is the Spec. -/

theorem impl_correct : ∀ n, impl n = permanentSpecN n := by
  intro n
  unfold impl
  by_cases h3 : 3 ≤ permanentDimension n
  · have h2 : ¬ permanentDimension n < 3 := by omega
    rw [if_neg h2]
    have hmain := spec_sparse (permanentDimension n) (permanentSeed n) h3
      (permanentDimension n) (by omega) 0
    rw [Nat.sub_self, rowsFrom_zero] at hmain
    rw [← hmain, permanentSpecN, spec_of_rows]
  · have h2 : permanentDimension n < 3 := by omega
    rw [if_pos h2]
    rw [spec_small _ _ h2, permanentSpecN]

end Submission
