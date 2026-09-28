import Spec

/-! Cost decomposition for the ca-rule110 candidate.

Why this exists: the v2 candidate replaced the list-based `initRowFor` with a
list-free bit accumulator, on the theory (recorded in the skill) that the init
was ~98.9% of the metric. Measured on the remote judge, v2 came out at
290.3M instructions vs the official list-based 290.5M -- a 0.06% difference,
i.e. no effect. So the decomposition behind that number is what needs
re-measuring, and the init is the first thing to isolate.

The judge counts PERF_COUNT_HW_INSTRUCTIONS on `impl n`. There is no PMU on
this VM (perf_event_paranoid=2, no perf binary), so wall-time here is a
RELATIVE proxy only -- never quote it as instructions. The judge is the only
instrument that produces real counts.

Three variants, so the fixed and per-step parts separate:
  initOnly  = biter 0 (initBits seed)      -- the init, no steps
  stepsOnly = biter 8 <fixed mask>         -- 8 steps, no init
  full      = biter (caSteps n) (initBits seed)   -- what the judge measures

Each is run on the SAME seed as the judge input so the magnitudes compare.
Repetitions are reported with a mean so a single slow call cannot pose as a win.
-/

namespace Decomp

def M : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

def bstep (m : Nat) : Nat :=
  (M ^^^ (((M ^^^ m) &&& (M ^^^ (((m >>> 1) ||| ((m &&& 1) <<< 255)) &&& M))) |||
          ((((m <<< 1) ||| (m >>> 255)) &&& M) &&& m &&& (((m >>> 1) ||| ((m &&& 1) <<< 255)) &&& M)))) &&& M

def biter : Nat → Nat → Nat
  | 0, m => m
  | t + 1, m => biter t (bstep m)

/-- v2's list-free init, verbatim. -/
def cellBit (seed i : Nat) : Bool :=
  if i = 0 then true
  else if i = 1 then false
  else (caMix32 (seed + (i + 1) * 0x9e3779b9)).testBit 31

def initBitsAux (seed i : Nat) (acc : Nat) : Nat :=
  if i = 0 then acc
  else initBitsAux seed (i - 1) ((acc <<< 1) ||| (if cellBit seed (i - 1) then 1 else 0))

def initBits (seed : Nat) : Nat := initBitsAux seed ruleWidth 0

def initOnly (seed : Nat) : Nat := biter 0 (initBits seed)

/-- 8 steps from a fixed, already-packed word: isolates the per-step cost from
the init without depending on how the init is written. -/
def stepsOnly : Nat := biter 8 0x0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f

def full (n : Nat) : Nat := biter (caSteps n) (initBits (caSeed n))

/-- The official list-based pipeline, for a same-seed comparison against `full`. -/
def official (n : Nat) : Nat :=
  biter (caSteps n) (encodeRow (initRowFor (caSeed n)))

/-- Consume a result so it cannot be optimised away.

`Nat.popcount` does NOT exist in this toolchain (v4.33.1) -- it was already
established when writing the sieve candidates, and re-typing it here cost a
build cycle.

A `2^n - 1` all-ones mask is the obvious stand-in but panics here
(`Nat.pow exponent is too big`) because `n` is the VALUE, ~256 bits, not a
bit-width. What is needed is a mask of FIXED width that still depends on
`v`. Modulo `2^32` keeps only the low 32 bits, which is enough to pin the work
(dead code cannot be eliminated: the accumulator is printed) while costing O(1)
and never panicking. The agreement check below is what guards against a digest
too weak to distinguish two wrong pipelines. -/
def digest (v : Nat) : Nat := v % 0x100000000

/-- Time `reps` calls, forcing each result into an accumulator that is printed.

The `digest` fold is what makes this a measurement at all. The first version
of this bench used `let _ := f n` and printed `0 us/call` for EVERY variant,
including the full pipeline -- not infinite speed, but dead code: a `let` whose
value is discarded is eliminated by the optimizer, so the computation never
ran. `IO.monoMsNow` is also only millisecond-granular, so a sub-ms call rounds
to 0 whether it took 0 or 900 us. Hence both fixes: consume the result, and
scale reps until the total clears the clock's resolution. -/
def bench (label : String) (f : Nat → Nat) (n : Nat) (reps : Nat) : IO Unit := do
  -- warm up once, also consumed
  let mut acc := digest (f n)
  let t0 ← IO.monoMsNow
  for _ in [0:reps] do
    acc := acc + digest (f n)
  let t1 ← IO.monoMsNow
  let total := t1 - t0
  IO.println s!"{label}  n={n} steps={caSteps n}  {reps * 1000 / max total 1} us/call  ({total} ms / {reps} reps, digest={acc})"

end Decomp

/-! ### Entry point

`main` must sit outside `namespace Decomp`: inside it the file compiles fine
but the exe fails to link with `undefined symbol: main` -- the C entry point
is looked up at the root, not inside a Lean namespace. -/

open Decomp in
def main : IO Unit := do
  -- the judge's three real inputs (run 315): steps 2, 4, 8
  let cases : List Nat := [12551916119, 18550129185, 34820276714]
  for n in cases do
    IO.println s!"-- n={n} steps={caSteps n} seed={caSeed n} --"
    bench "initOnly  " initOnly (caSeed n) 2000
    bench "stepsOnly " (fun _ => stepsOnly) n 2000
    bench "full(v2)  " full n 2000
    bench "official " official n 2000
    -- agreement, so a "fast" variant cannot be posing as a correct one
    if full n == official n then
      IO.println "  agreement: MATCH"
    else
      IO.println "  agreement: ***MISMATCH***"
  -- pure step scaling: 0 / 1 / 2 / 4 / 8 steps on the same word, no init at all
  IO.println "-- step scaling (no init) --"
  for t in [0, 1, 2, 4, 8] do
    let mut acc := 0
    let t0 ← IO.monoMsNow
    for _ in [0:2000] do
      acc := acc + digest (biter t 0x0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f)
    let t1 ← IO.monoMsNow
    IO.println s!"  biter {t}: {(t1 - t0) / 2} us/call (digest={acc})"
