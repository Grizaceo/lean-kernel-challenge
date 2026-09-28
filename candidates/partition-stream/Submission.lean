import Spec

/-! # partition — block-streaming coin-change DP (speed probe, proof pending)

Same recurrence and same values as the Spec; only the *shape* of the row update
changes. The shipped `partition-foldl` recomputes each cell as an independent
multiplicity sum, and every summand re-walks the row with `getD`:

    new[m] = Σ_j t.getD (m - j*d) 0

so a row costs O(n²/d) list-cell traversals and the whole run O(n³) overall.

The identity exploited here is the same one the Spec's own recurrence is built
on, one level up. Grouping the multiplicity sum by its first term:

    Σ_j t[m - j*d] = t[m] + Σ_i t[m - (i+1)*d] = t[m] + new[m - d]

so `new[m] = t[m] + new[m - d]`, with `new[m] = 0` for `m < d`. This is
Euler's recurrence for a single part size, not a new theorem.

Since `new[m]` depends only on `new[m - d]`, positions split into `d` residue
classes modulo `d`, and a *block* of `d` consecutive positions needs exactly the
previous block of `d` values and nothing else:

    new[b*d + i] = t[b*d + i] + new[(b-1)*d + i] = t[b*d + i] + prevBlock[i]

so one `zipWith` produces `d` cells in O(d) and a whole row costs O(n) instead
of O(n²/d). The last block may be shorter than `d`; its predecessor is always
full length (or the `d`-length zero block for the first), so `zipWith`
truncation loses nothing: for `m < d`, `new[m] = t[m]` via the zero block.

`chunks` recurses on an explicit fuel (an upper bound on the number of
blocks, `t.length`), which keeps the recursion structural on `Nat` and the
kernel reduction loop-free of well-founded checks.
-/

namespace Submission

/-- The element of `xs` at index `i`, or `0` past the end. -/
def nthNat : List Nat → Nat → Nat
  | [], _ => 0
  | x :: _, 0 => x
  | _ :: xs, i + 1 => nthNat xs i

/-- Split `l` into consecutive blocks of length `d`, consuming one unit of
`fuel` per block. Fuel is an upper bound on the block count (`l.length` works),
so exhaustion coincides with the end of `l`. -/
def chunks (d : Nat) : Nat → List Nat → List (List Nat)
  | 0, _ => []
  | _ + 1, [] => []
  | fuel + 1, l => l.take d :: chunks d fuel (l.drop d)

/-- Fold the blocks, each new block being its source block plus the block that
precedes it in the same residue class. -/
def zipBlocks : List Nat → List (List Nat) → List Nat
  | _, [] => []
  | prev, blk :: rest =>
    let bn := blk.zipWith (· + ·) prev
    bn ++ zipBlocks bn rest

/-- The row for part size `d`, given the previous row `t`. -/
def updRow (d : Nat) (t : List Nat) : List Nat :=
  zipBlocks (List.replicate d 0) (chunks d t.length t)

/-- Initial row for parts ≤ 0: 1 at m = 0, 0 elsewhere. -/
def initTable (n : Nat) : List Nat := 1 :: List.replicate n 0

/-- Apply part sizes 1 … k to the current row. -/
def tableIt : Nat → List Nat → List Nat
  | 0, t => t
  | k + 1, t => tableIt k (updRow (k + 1) t)

def impl (n : Nat) : Nat := nthNat (tableIt n (initTable n)) n

end Submission
