import Spec

/-! # partition — Euler's pentagonal recurrence, computed bottom-up.

## The baseline

The Spec is `partitionSpec n = partAux n n` where

```
partAux k n = ((List.range (n / (k+1) + 1)).map (fun j => partAux k (n - j*(k+1)))).foldl (·+·) 0
```

with **no memoization**, so the same `partAux k m` is recomputed exponentially
many times. The Spec's own docstring concedes it: "Deliberately naive …
submissions are expected to compute the value efficiently."

Measured on the judge's inputs (playground run 272): 531M / 1.50B / 3.69B
instructions at n = 14 / 22 / 32. Rank 1 sits at 1,441,321 — a factor ~2,560
below the baseline.

## The idea

Euler's pentagonal theorem gives `p(n)` from a recurrence that only ever refers
to *strictly smaller* arguments:

```
p(0) = 1
p(n) = Σ_{k≥1} (-1)^(k+1) · ( p(n - k(3k-1)/2) + p(n - k(3k+1)/2) )
```

Only `k` with `k(3k-1)/2 ≤ n` contribute, so the walk is `O(√n)` long — 5
values of `k` at n = 32.

**No division and no `%` anywhere.** The pentagonal numbers are generated
incrementally. With `g1(k) = k(3k-1)/2` and `g2(k) = k(3k+1)/2`,

```
g1(k+1) = g1(k) + (3k+1)        g2(k+1) = g2(k) + (3k+2)
```

so both the positions and their strides advance by addition, and the sign
alternates a carried `Bool` instead of being read off a parity test. This
matters: a single `Nat.mod` costs on the order of 10^5 kernel instructions on
this judge — measured on `primecount`, where 13,200 mods accounted for
essentially all of a 1.73B total.

## Bottom-up, not recursive

An earlier version of this candidate evaluated the recurrence by direct
recursion, `pInt n = Σ pInt (n - g)`. That is still exponential for the same
reason the Spec is: every one of the `O(√n)` references at level `n` triggers a
*fresh* subtree and nothing is shared. Measured on this machine it returned
instantly at n = 40 and had not finished at n = 50 — the same defect as the
baseline with a smaller constant, and it would not have survived the judge's own
n = 32 neighbourhood.

So the values are filled **once, in ascending order**, into a list. Level `m`
reads only levels `< m`, which are already final. `psum` therefore performs no
recursive call back into the table at all — it is a single `O(√m)` walk — and
the only recursion is the one on the ascending counter.

Carried in `Int` because the recurrence is a signed alternating sum, converted
to `Nat` at the boundary. `p(n) ≥ 0` for all `n ≥ 0`, so `Int.toNat` is exact.

## Note on the walk state

`Walk` is a plain `structure` rather than a pile of positional `Nat`s. Lean's
equation compiler accepts at most three patterns per match alternative, so a
nine-argument `def` cannot be given a structural equation at all; bundling the
five counters into one inductive-free record leaves `fuel` as the single matched
argument and keeps the recursion structural. (The same limit is why an earlier
`permanent` attempt had to bundle state into a pair.)

## Proof status

`impl_correct` is not proved. Semantic equivalence is established executably:
`candidates/partition-crosscheck` compares this `impl` against `partitionSpec`
on the judge's own inputs (14 / 22 / 32) and exhaustively over 0..79 — the
upper bound being where the unmemoized Spec stops being usable, located by
timing `partitionSpec` alone (instant to n = 70, unfinished at n = 80). The Spec
is a *different* recurrence, so agreement is an independent check rather than a
restatement of the same formulas.
-/

namespace Submission

/-- The element of `xs` at index `i`, or `0` past the end. -/
def nthInt : List Int → Nat → Int
  | [], _ => 0
  | x :: _, 0 => x
  | _ :: xs, i + 1 => nthInt xs i

/-- Position of the pentagonal walk: `g1 = k(3k-1)/2`, `g2 = k(3k+1)/2`, and
the strides `3k+1`/`3k+2` that carry them to the next `k`. `pos` is the sign for
the current `k`, which is positive when `k` is odd. -/
structure Walk where
  g1 : Nat
  g2 : Nat
  step1 : Nat
  step2 : Nat
  pos : Bool
  deriving Repr

/-- The signed pentagonal sum giving `p(m)` from `tbl`, which holds the
already-final values `p(0..m-1)`.

`st` is advanced by the strides, so the next pentagonal numbers are reached by
addition and never by division. The walk ends when `g1 > m`, at which point no
further pentagonal number is in range. -/
def psum : List Int → Nat → Walk → Nat → Int
  | _, _, _, 0 => 0
  | tbl, m, st, fuel + 1 =>
    if st.g1 > m then 0
    else
      let s := nthInt tbl (m - st.g1)
        + (if st.g2 ≤ m then nthInt tbl (m - st.g2) else 0)
      let here := if st.pos then s else -s
      here + psum tbl m
        { g1 := st.g1 + st.step1, g2 := st.g2 + st.step2
          step1 := st.step1 + 3, step2 := st.step2 + 3, pos := !st.pos }
        fuel

/-- `p(0..m)` extended upward, given `tbl` holding `p(0..m-1)`.

`m` is the value being appended, and it starts at 1 because `p(0) = 1` is
already in the seed list. So `build tbl k` appends exactly `k` values, ending
with `p(k)` at index `k`.

`psum` is given its own budget rather than `build`'s remaining fuel. Sharing the
counter looks economical and is wrong: `build`'s fuel is nearly spent by the
time the table has grown, so the last few `psum` calls hit their `fuel = 0` base
case and return a *partial* pentagonal sum. That is not an under-fuel crash but
a silent wrong answer — on n = 14 it produced 177 where the Spec gives 135. -/
def build : List Int → Nat → Nat → List Int
  | tbl, _, 0 => tbl
  | tbl, m, fuel + 1 =>
    -- g1(1) = 1, g2(1) = 2; strides 3k+1 = 4 and 3k+2 = 5 at k = 1.
    build (tbl ++ [psum tbl m ⟨1, 2, 4, 5, true⟩ (m + 1)]) (m + 1) fuel

/-- The partition function: the number of ways to write `n` as a sum of
positive integers, disregarding order.

`build [1] 1 (n + 1)` appends `p(1)` through `p(n)`, giving a table of `n + 1`
entries whose element at index `n` is `p(n)`. -/
def impl (n : Nat) : Nat :=
  (nthInt (build [1] 1 (n + 1)) n).toNat

end Submission
