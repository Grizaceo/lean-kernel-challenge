/-!
A/B harness for the ca-rule110 initial row. NOT a submission.

Purpose (2026-09-27): with the local instruction counter (scripts/icount.c) the
per-cell cost of the init is measurable and deterministic. The decomposition
showed 10.9M instructions per cell while a bare `caMix32` costs under 2M, so
>=82% of the init cost is per-cell scaffolding, not the hash. This module holds
several formulations of the SAME value so they can be A/B'd in isolation,
without paying the cost of re-proving `impl_correct` first.

  initBits    -- the shipped v2 formulation (growing 256-bit accumulator)
  initBits3   -- incremental mix argument + hoisted i=0/i=1 guards
  initBits4   -- byte lanes: 32-bit accumulators, combined once at the end

`packTo k v lo acc` is the shared primitive: it walks the mix argument `v`
downwards by 0x9e3779b9 per cell, emitting cell `k-1`, and stops once cells
below `lo` would be touched. Cell `c` uses mix argument `seed + (c+1) * K`,
exactly as the spec's `initRowFor` does, so the incremental decrement is the
same value as recomputing the product each cell (exact Nat arithmetic).
-/

namespace InitAB

def ruleWidth : Nat := 256

/-- Copied verbatim from problems/ca-rule110/Spec.lean so this module needs no
import of the Spec lib and the A/B compares like with like. -/
def caMix32 (x : Nat) : Nat :=
  let x := ((x ^^^ (x >>> 16)) * 0x7feb352d) &&& 0xffffffff
  let x := ((x ^^^ (x >>> 15)) * 0x846ca68b) &&& 0xffffffff
  (x ^^^ (x >>> 16)) &&& 0xffffffff

/-! ### A: shipped v2 formulation -/

def cellBit (seed i : Nat) : Bool :=
  if i = 0 then true
  else if i = 1 then false
  else (caMix32 (seed + (i + 1) * 0x9e3779b9)).testBit 31

def initBitsAux (seed i : Nat) (acc : Nat) : Nat :=
  if i = 0 then acc
  else initBitsAux seed (i - 1) ((acc <<< 1) ||| (if cellBit seed (i - 1) then 1 else 0))

def initBits (seed : Nat) : Nat :=
  initBitsAux seed ruleWidth 0

/-! ### shared primitive -/

/-- Emit cells `k-1, k-2, ..., lo` (cell `c` from mix argument `v - (k-1-c)*K`),
prepending each bit at position 0 and shifting the accumulator left. -/
def packTo (k v lo acc : Nat) : Nat :=
  if k < lo + 1 then acc
  else packTo (k - 1) (v - 0x9e3779b9) lo
    ((acc <<< 1) ||| (if (caMix32 v).testBit 31 then 1 else 0))

/-! ### B: incremental mix argument, hoisted guards -/

def initBits3 (seed : Nat) : Nat :=
  (packTo ruleWidth (seed + ruleWidth * 0x9e3779b9) 2 0 <<< 2) ||| 1

/-! ### C: byte lanes -- accumulator never exceeds 32 bits -/

/-- Lane `l` covers cells `[256-32(l+1) .. 255-32l]`, returned with the lane's
lowest cell at bit 0, so the caller shifts it into place once. -/
def laneAt (seed l : Nat) : Nat :=
  let cHi := 255 - 32 * l
  let cLo := 224 - 32 * l
  packTo (cHi + 1) (seed + (cHi + 1) * 0x9e3779b9) cLo 0

/-- The last lane stops at cell 2: cells 0 and 1 are FIXED by the spec
(true, false) and must never be passed through the mixer. -/
def lastLane (seed : Nat) : Nat :=
  (packTo 32 (seed + 32 * 0x9e3779b9) 2 0 <<< 2) ||| 1

def initBits4 (seed : Nat) : Nat :=
  ((laneAt seed 0 <<< 224) ||| (laneAt seed 1 <<< 192) |||
   (laneAt seed 2 <<< 160) ||| (laneAt seed 3 <<< 128) |||
   (laneAt seed 4 <<< 96) ||| (laneAt seed 5 <<< 64) |||
   (laneAt seed 6 <<< 32) ||| lastLane seed)

end InitAB
