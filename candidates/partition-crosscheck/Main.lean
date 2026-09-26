import Part

/-! Cross-check of the *actual* `Submission.lean` candidate for `partition`
against the Spec's own `partitionSpec`.

`Part.lean` is a byte-for-byte copy of the candidate, so this measures exactly
the bytes that would be uploaded.

The Spec computes `partAux n n` by multiplicity of the largest allowed part,
which is a genuinely different recurrence from Euler's pentagonal theorem used
here. So agreement is an independent check, not a restatement of the same
formulas.

## Why the sweep stops at 79 — measured, not guessed

`partitionSpec` is unmemoized and exponential, so the limit belongs to the
*oracle*, not the candidate. The boundary was located with
`candidates/partition-crosscheck/OracleCost.lean`, timing `partitionSpec` alone:

| n | 10 … 32 (judge inputs) | 33 … 40 | 45 … 60 | 61 … 70 | 80 |
|---|---|---|---|---|---|
| wall time | 0 ms | 0 ms | 0 ms | 0 ms | does not finish in 200 s |

So the cliff sits between n = 70 and n = 80. 0..79 covers it with margin and
still runs in seconds. The measured inputs are only n = 14 / 22 / 32, so this
is already a far wider check than the judge needs.

The range also covers every branch of the candidate: the `p(0) = 1` base case,
the `_, 0 => 0` guard, the `g2 ≤ n` guard (n = 2 and n = 7 fall between
pentagonal pairs), the `g1 > n` walk terminator, and the fuel bound.
-/

open Submission

def check (n : Nat) : IO Unit := do
  let want := partitionSpec n
  let got := impl n
  if got == want then
    IO.println s!"n={n}  MATCH  p({n})={got}"
  else
    IO.println s!"n={n}  ***MISMATCH***  spec={want} euler={got}"
    IO.Process.exit 1

def main : IO Unit := do
  -- The judge's own inputs first: these are the ones that get timed.
  IO.println "== judge inputs =="
  for n in [14, 22, 32] do check n
  -- Exhaustive sweep, bounded by the measured oracle cliff (70 ok, 80 not).
  IO.println "== exhaustive 0..79 =="
  for n in [0:80] do check n
  IO.println "ALL MATCH (judge inputs 14/22/32, exhaustive 0..79)"
