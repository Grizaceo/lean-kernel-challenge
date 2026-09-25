import CrossCheck

/-! Executes the cross-check on the exact inputs the judge uses (steps 2/4/8)
plus a small sweep for confidence. -/

open CrossCheck

def check (n : Nat) : IO Unit := do
  let a := refImpl n
  let b := v2 n
  if a = b then
    IO.println s!"n={n}  MATCH  (value {a})"
  else
    IO.println s!"n={n}  ***MISMATCH***"
    IO.println s!"  spec={a}"
    IO.println s!"  v2  ={b}"
    IO.Process.exit 1

def main : IO Unit := do
  -- the judge's three inputs
  for n in [2, 4, 8] do check n
  -- confidence sweep
  for n in [0, 1, 3, 5, 6, 7, 9, 16, 17, 31, 33, 64, 100, 255, 256, 1000, 65535, 65536] do
    check n
  IO.println "ALL MATCH"
