import Mertens

/-! Cross-check of the *actual* `Submission.lean` candidate against Mathlib's
Möbius sum, which is the Spec. Executable, not a theorem.

`Mertens.lean` is a byte-for-byte copy of the candidate with only the namespace
renamed, so this measures exactly what would be uploaded. -/

open Submission

def refImpl (n : Nat) : Int := mertensSpec n

def check (n : Nat) : IO Unit := do
  let want := refImpl n
  let got := impl n
  if got == want then
    IO.println s!"n={n}  MATCH  {got}"
  else
    IO.println s!"n={n}  ***MISMATCH***  spec={want} got={got}"
    IO.Process.exit 1

def main : IO Unit := do
  -- Judge inputs first: these are the ones that get timed.
  IO.println "== judge inputs =="
  for n in [100, 200, 300] do check n
  -- Exhaustive small sweep. This is where a wrong outer-loop bound, a bad
  -- fuel count, or an off-by-one in the `μ(0) = 0` start shows up.
  IO.println "== exhaustive 0..320 =="
  for n in [0:321] do check n
  -- Values that stress the `√n` trap documented in the module: numbers whose
  -- largest prime factor greatly exceeds `√n`.
  IO.println "== semiprimes with a large factor =="
  for n in [494, 646, 899, 1001] do check n
  IO.println "ALL MATCH (exhaustive 0..320, incl. judge inputs 100/200/300)"
