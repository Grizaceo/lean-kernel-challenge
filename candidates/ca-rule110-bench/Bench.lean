import Spec

/-! Benchmark harness: times `impl` alone (what the judge actually measures).
No theorems, no proofs — just the definitions, compiled and #eval'd. -/

namespace Bench

def M : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

def bstep (m : Nat) : Nat :=
  (M ^^^ (((M ^^^ m) &&& (M ^^^ (((m >>> 1) ||| ((m &&& 1) <<< 255)) &&& M))) |||
          ((((m <<< 1) ||| (m >>> 255)) &&& M) &&& m &&& (((m >>> 1) ||| ((m &&& 1) <<< 255)) &&& M)))) &&& M

def biter : Nat → Nat → Nat
  | 0, m => m
  | t + 1, m => biter t (bstep m)

/-- v2: list-free initial word. -/
def cellBit (seed i : Nat) : Bool :=
  if i = 0 then true
  else if i = 1 then false
  else (caMix32 (seed + (i + 1) * 0x9e3779b9)).testBit 31

def initBitsAux (seed i : Nat) (acc : Nat) : Nat :=
  if i = 0 then acc
  else initBitsAux seed (i - 1) ((acc <<< 1) ||| (if cellBit seed (i - 1) then 1 else 0))

def initBits (seed : Nat) : Nat :=
  initBitsAux seed ruleWidth 0

def implV2 : Nat → Nat := fun n =>
  biter (caSteps n) (initBits (caSeed n))

/-- v1 (official example): list-based initial row. -/
def implV1 : Nat → Nat := fun n =>
  biter (caSteps n) (encodeRow (initRowFor (caSeed n)))

end Bench
