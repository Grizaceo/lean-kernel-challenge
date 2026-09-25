import Spec

/-! # mertens — division-free Möbius sieve.

## The baseline

`impl n = ∑ k ∈ Finset.range (n+1), moebiusByFactors k` where
`moebiusByFactors n = if n.primeFactorsList.Nodup then (-1)^len else 0`.
Every `k` costs a full trial factorisation up to `√k`. Measured on the judge's
inputs (playground run 280): ~2.0B instructions at n=100 and n=200, ~1.9B at
n=300. Rank 1 sits at ~1.56M — roughly 1200× below.

## The idea

Two facts make one linear sieve with **no `Nat.mod` anywhere** possible:

1. `μ(k) = 0` unless `k` is squarefree; otherwise `μ(k) = (-1)^ω(k)`, with `ω`
   the number of *distinct* prime factors.
2. Each prime contributes independently: `k` is squareful iff some `p²` divides
   it, and `ω(k)` is the number of primes dividing it.

So three bitmasks over `0..n` suffice, all built by runs that advance by
addition (`i ← i + step`), never by division:

- `par` — bit `k` toggled once per distinct prime divisor of `k`; its final
  value is `ω(k) mod 2`.
- `sq` — bit `k` set iff `k` is divisible by some `p²`.
- `comp` — bit `k` set iff `k` is composite, so the outer loop can reject
  candidates without any primality test.

## The trap: the outer loop must reach `p ≤ n`, not just `√n`

A `√n`-bounded walk silently produces wrong answers. For `k = 298 = 2 · 149`
with `n = 300`, the prime 149 satisfies `149 > √300 ≈ 17.3`. A walk stopping at
`√n` never toggles `k = 298` for 149, reads `ω(298)` as 1 instead of 2, and
returns `μ(298) = -1` instead of `+1`. The toggle walk therefore runs over all
primes up to `n` — still `O(n log log n)`, and only ~540 toggles at n = 300.

## Why xor is right for `par` but wrong for `sq`

The `par` runs *must* overlap: that is precisely how `ω` accumulates. Within one
run the positions are distinct, so each is toggled once per prime, and xor
gives the parity. The `sq` runs, by contrast, must not undo each other — a
number divisible by two different squares is still squareful — so they use `|||`
(set) rather than `^^^` (toggle). Getting this backwards resurrects squareful
numbers exactly as it did in the `primecount` sieve.

## Proof status

`impl_correct` is not proved here. Semantic equivalence is established
executably: `candidates/mertens-crosscheck` compares this `impl` against
Mathlib's `mertensSpec` on all of `0..320`, on the judge's own inputs
(100 / 200 / 300), and on semiprimes whose largest prime factor exceeds `√n`
(494, 646, 899, 1001) — all match. The remaining obligation for a competitive
submission is the formal proof, which needs `μ`'s multiplicativity stated
directly rather than via `Nat.squarefree_iff_nodup_primeFactorsList`.
-/

namespace Submission

/-- Toggle the bit at positions `start, start+step, … ≤ n`. -/
def runToggle (mask n step start : Nat) : (fuel : Nat) → Nat
  | 0 => mask
  | fuel + 1 =>
    if start > n then mask
    else runToggle (mask ^^^ (1 <<< start)) n step (start + step) fuel

/-- Set the bit at positions `start, start+step, … ≤ n`. Or, not toggle: runs
for different primes overlap and a number divisible by two squares is still
squareful, so a bit already set must stay set. -/
def runSet (mask n step start : Nat) : (fuel : Nat) → Nat
  | 0 => mask
  | fuel + 1 =>
    if start > n then mask
    else runSet (mask ||| (1 <<< start)) n step (start + step) fuel

/-- One pass over `p = 2 … n`, building the parity-of-`ω` mask and the
squareful mask. Every inner run is given fuel `n+1`, which is always
sufficient; the `start > n` guard ends each walk, and unspent fuel costs
nothing in the kernel. -/
def sieve (n : Nat) : Nat × Nat := Id.run do
  let mut par := 0
  let mut comp := 0
  let mut sq := 0
  let mut p := 2
  while p ≤ n do
    if (comp >>> p) &&& 1 == 0 then
      par := runToggle par n p p (n + 1)
      comp := runSet comp n p (2 * p) (n + 1)
      let p2 := p * p
      if p2 ≤ n then
        sq := runSet sq n p2 p2 (n + 1)
    p := p + 1
  return (par, sq)

/-- `∑_{k=1}^{n} μ(k)`, reading the three masks. `μ(0) = 0` so the walk starts
at `k = 1`. -/
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

/-- The Mertens function `M(n) = ∑_{k=0}^{n} μ(k)`. -/
def impl (n : Nat) : Int :=
  let (par, sq) := sieve n
  msumAux par sq n 1 (n + 1)

end Submission
