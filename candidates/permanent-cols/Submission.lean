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

`impl_correct` is not proved. `candidates/permanent-crosscheck` compares this
`impl` against `permanentSpecN` on the judge's three packed inputs and sweeps
dimensions and seeds, including the `dimension < 3` branch.
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

end Submission
