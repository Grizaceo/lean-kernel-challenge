-- Times both init strategies on the real judge inputs (steps 2/4/8).
-- The judge counts PERF_COUNT_HW_INSTRUCTIONS on `impl n`; we have no PMU
-- locally, so wall-time is a relative proxy only (see skill: lean-kernel-rules).

open Bench

-- Real judge inputs, decoded (steps = n >>> 32, seed = n &&& 0xffffffff)
def cases : List (Nat × Nat × Nat) :=
  [ (12551916119, 2, 3961981527)
  , (18550129185, 4, 1370260001)
  , (34820276714, 8, 460538346)
  ]

def timeIt (label : String) (f : Nat → Nat) (n : Nat) : IO Unit := do
  let t0 ← IO.monoMsNow
  let _v := f n
  let t1 ← IO.monoMsNow
  IO.println s!"{label} n={n}: {t1 - t0} ms"

def main : IO Unit := do
  IO.println "-- v1 (official: list-based initRowFor) --"
  for (n, _, _) in cases do
    timeIt "v1" implV1 n
  IO.println "-- v2 (candidate: list-free initBits) --"
  for (n, _, _) in cases do
    timeIt "v2" implV2 n
  -- equality check: v2 must agree with v1 on these inputs
  IO.println "-- agreement --"
  for (n, _, _) in cases do
    if implV1 n == implV2 n then
      IO.println s!"n={n}: MATCH"
    else
      IO.println s!"n={n}: MISMATCH  v1={implV1 n}  v2={implV2 n}"
