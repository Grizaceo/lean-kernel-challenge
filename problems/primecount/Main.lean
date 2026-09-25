import Sieve

/-! Cross-check of the *actual* `Submission.lean` candidate against the Spec
reference. Executable, not a theorem: the judge only times `impl n`, so
semantic equivalence is the thing that must be established before spending a
run on instruction counts.

`Sieve.lean` is a byte-for-byte copy of the candidate with only the namespace
renamed, so this measures exactly what would be uploaded. -/

open Submission

def refImpl (n : Nat) : Nat := Nat.primeCounting n

def check (n : Nat) : IO Unit := do
  let want := refImpl n
  let got := impl n
  if got == want then
    IO.println s!"n={n}  MATCH  {got}"
  else
    IO.println s!"n={n}  ***MISMATCH***  ref={want} sieve={got}"
    IO.Process.exit 1

def main : IO Unit := do
  -- The judge's own inputs first, since these are what get timed.
  IO.println "== judge inputs =="
  for n in [50, 150, 600] do check n
  -- Then an exhaustive sweep over small values, where boundary conditions in
  -- the mask width ((n+1)/2) and the `2 ≤ n` special case are most likely to
  -- break, plus a sparse large sweep to confirm the logic scales.
  IO.println "== exhaustive 0..1200 =="
  for n in [0:1201] do check n
  IO.println "== sparse large =="
  for n in [5000, 20000, 100000] do check n
  IO.println "ALL MATCH (exhaustive 0..1200, incl. judge inputs 50/150/600)"
