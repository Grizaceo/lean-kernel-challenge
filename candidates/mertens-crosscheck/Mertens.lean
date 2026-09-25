import Spec

/-! # mertens — division-free Möbius sieve.

## The baseline

`impl n = ∑ k ∈ Finset.range (n+1), moebiusByFactors k` where
`moebiusByFactors n = if n.primeFactorsList.Nodup then (-1)^len else 0`.
Every `k` costs a full trial factorisation up to `√k`. Measured on the judge's
inputs (playground run 280): ~2.0B instructions at n=100 and n=200, ~1.9B at
n=300. Rank 1 sits at ~1.56M.

## The idea

Two facts make one linear sieve with **no `Nat.mod` anywhere** possible:

1. `μ(k) = 0` unless `k` is squarefree; otherwise `μ(k) = (-1)^ω(k)`, with `ω`
   the number of *distinct* prime factors.
2. Each prime contributes independently: `k` is squareful iff some `p²` divides
   it, and `ω(k)` is the number of primes that divide it.

So three bitmasks over `0..n` suffice, all built by runs that advance by
addition (`m ← m + step`), never by division:

- `par` — bit `k` toggled once per distinct prime divisor of `k`; its final
  value is `ω(k) mod 2`.
- `sq` — bit `k` set iff `k` is divisible by some `p²`.
- `comp` — bit `k` set iff `k` is composite, used only to test primality of `p`
  as the outer loop walks `2, 3, 4, …`.

## Why the outer loop must reach `p ≤ n`, not just `√n`

This is the trap that a `√n`-bounded walk falls into. For `k = 298 = 2 · 149`
with `n = 300`, the prime 149 satisfies `149 > √300 ≈ 17.3`. A walk that stops
at `√n` never toggles `k = 298` for 149, so `ω(298)` is read as 1 instead of 2
and `μ(298)` comes out as `-1` instead of `+1`. The toggle walk therefore runs
over **all** primes up to `n`, not just the small ones — which is still
`O(n log log n)` and, at n = 300, only ~540 toggles.
-/

namespace MT

def refImpl (n : Nat) : Int := mertensSpec n

/-- Toggle the bit at `m` for `m = start, start+step, … ≤ n`.

Xor is correct here and only here: the runs for *different* primes are
supposed to overlap, since that is exactly how `ω` accumulates. Positions
inside one run are distinct, so each is toggled once per prime. -/
def runToggle (mask n step start : Nat) : (fuel : Nat) → Nat
  | 0 => mask
  | fuel + 1 =>
    if start > n then mask
    else runToggle (mask ^^^ (1 <<< start)) n step (start + step) fuel

/-- Set the bit at `m` for `m = start, start+step, … ≤ n`. Or, not xor: runs for
different primes overlap, and a squareful number must stay marked. -/
def runSet (mask n step start : Nat) : (fuel : Nat) → Nat
  | 0 => mask
  | fuel + 1 =>
    if start > n then mask
    else runSet (mask ||| (1 <<< start)) n step (start + step) fuel

/-- One pass: build `(parity of ω, composite flags, squareful flags)`.
Fuel for every inner run is `n+1`, which is always enough; the `start > n`
guard stops the walk, and unused fuel costs nothing in the kernel. -/
def sieve (n : Nat) : Nat × Nat × Nat := Id.run do
  let mut par := 0
  let mut comp := 0
  let mut sq := 0
  let mut p := 2
  while p ≤ n do
    if (comp >>> p) &&& 1 == 0 then
      -- `p` is prime: toggle it into every multiple (this counts `p` once per
      -- multiple, and multiples of p² still get exactly one toggle, which is
      -- what "distinct prime factors" means).
      par := runToggle par n p p (n + 1)
      -- Mark 2p, 3p, … composite so later candidates can be rejected.
      comp := runSet comp n p (2 * p) (n + 1)
      -- Mark p², 2p², … squareful.
      let p2 := p * p
      if p2 ≤ n then
        sq := runSet sq n p2 p2 (n + 1)
    p := p + 1
  return (par, comp, sq)

/-- `∑ k ∈ [1, n] μ(k)`. Starts at `k = 1` because `μ(0) = 0`. -/
def msumAux (par sq n k : Nat) : (fuel : Nat) → Int
  | 0 => 0
  | fuel + 1 =>
    if k > n then 0
    else
      let term : Int :=
        if (sq >>> k) &&& 1 == 1 then 0
        else if (par >>> k) &&& 1 == 1 then -1
        else 1
      term + msumAux par sq n (k + 1) fuel

def impl (n : Nat) : Int :=
  let (par, _, sq) := sieve n
  msumAux par sq n 1 (n + 1)

end MT
