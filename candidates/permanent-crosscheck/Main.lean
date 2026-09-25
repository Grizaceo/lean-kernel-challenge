import Perm

/-! Cross-check of the *actual* `Submission.lean` candidate for `permanent`
against the Spec's own `permanentSpecN`.

`Perm.lean` is a byte-for-byte copy of the candidate, so this measures exactly
the bytes that would be uploaded.

The three judge inputs are the packed constants `(dimension <<< 32) | seed` taken
from playground run 273's metric slots — dimension 6, 12 and 16. Dimension 16 is
the one that gets timed at 131.7B instructions; the Spec needs ~17s and 5.1 GB
for it, so the sweep below stops at dimension 9 and the judge inputs are checked
one at a time rather than in a loop.
-/

open Submission

def check (label : String) (n : Nat) : IO Unit := do
  let want := permanentSpecN n
  let got := impl n
  if got == want then
    IO.println s!"{label}  MATCH  n={n} dim={permanentDimension n} per={got}"
  else
    IO.println s!"{label}  ***MISMATCH*** n={n} spec={want} sparse={got}"
    IO.Process.exit 1

def pack (d s : Nat) : Nat := (d <<< 32) ||| (s &&& 0xffffffff)

def main : IO Unit := do
  -- The judge's own inputs (run 273), smallest first so a failure is cheap.
  IO.println "== judge inputs (run 273) =="
  check "R1 6x6 " 28064292647
  check "R2 12x12" 53794586207
  check "R3 16x16" 71077100717
  -- Dimensions below 3 exercise the Spec's `fullAux` branch (all entries 1).
  IO.println "== dimension < 3 branch =="
  for d in [0, 1, 2] do
    for s in [0, 1, 7, 0xffffffff] do
      check s!"d={d} s={s}  " (pack d s)
  -- A seed/dimension sweep over the sparse branch, several seeds so the
  -- off-diagonal columns differ and collisions with the diagonal get exercised.
  IO.println "== sparse sweep d=3..9 =="
  for d in [3:10] do
    for s in [0, 1, 12345, 0x9e3779b9, 0xffffffff] do
      check s!"d={d} s={s}  " (pack d s)
  IO.println "ALL MATCH (judge inputs 6/12/16, d<3 branch, sparse sweep 3..9)"
