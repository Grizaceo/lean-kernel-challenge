import Sieve

open PC

/-- Two counting strategies, so the choice is made on measurement rather than
taste. (`Nat.popcount` does not exist in this toolchain — checked, not assumed.) -/
def countByShift (m : Nat) : (fuel : Nat) → Nat
  | 0 => 0
  | fuel + 1 => if m = 0 then 0 else (m &&& 1) + countByShift (m >>> 1) (fuel - 1)

/-- Count via repeated `m &&& (m-1)`, which drops the lowest set bit. The loop
ends when the mask is exhausted, so the cost tracks the number of primes found
rather than the mask width. -/
def countByClearLowest (m : Nat) : (fuel : Nat) → Nat
  | 0 => 0
  | fuel + 1 => if m = 0 then 0 else 1 + countByClearLowest (m &&& (m - 1)) (fuel - 1)

def main : IO Unit := do
  for n in [50, 150, 600] do
    let m := sieveLoop (oddMask n) n (fullMask n) 3 n
    let a := countByShift m (n + 2)
    let c := countByClearLowest m (n + 2)
    IO.println s!"n={n}: shift={a} clearlow={c}  agree={a == c}"
  -- Larger n: the sweep must still hold, and the mask grows.
  for n in [2000, 20000, 100000] do
    let got := impl n
    let want := refImpl n
    IO.println s!"n={n}: impl={got} ref={want} agree={got == want}"
