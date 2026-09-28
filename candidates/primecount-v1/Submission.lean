import Spec

/-!
# primecount: cheap trial-division primality instead of `decide (Nat.Prime _)` — MEASUREMENT ONLY

`Nat.primeCounting n = Nat.count Nat.Prime (n + 1)` and
`Nat.count p m = (List.range m).countP p`, so the reference pays for a decision
of `Nat.Prime k` at every `k` in `[0, n]`. Deciding `Nat.Prime k` unfolds a
`∀ d < k, d ∣ k → d = 1 ∨ d = k` through a `Decidable` instance, which is why
the reference costs 3.6 billion instructions at n = 12 — about 23 million per
candidate.

The question this file exists to answer is not "is this correct" but "is it
worth proving correct": if replacing that decision with plain
`Nat.mul` / `Nat.gt` / `Nat.mod` is not a large win, there is no point building
the equivalence proof. So this candidate deliberately has NO `impl_correct`
yet. measure.py only needs the official `impl n = v` replay, so it is
measurable as-is.

Both loops recurse structurally (on `d` and on `m` respectively) so the
elaborator infers termination and no `termination_by` is needed. An earlier
version spelled the decreases out by hand and only got "2 parameters bound in
termination_by, but the body binds 0" — the compiler had already settled it as
structural, so the annotation was both wrong and unnecessary.
-/

namespace Submission

/-- Primality using only `Nat.mul` / `Nat.le` / `Nat.mod` / `Nat.beq`.
Lean's own `List.any` and `List.count` are already structural recursion in the
library, so nothing here needs a termination proof of its own. -/
def isPrime (m : Nat) : Bool :=
  if m < 2 then false
  else !((List.range (m + 1)).any fun d =>
    decide (2 ≤ d) && (d * d ≤ m) && (m % d == 0))

def impl (n : Nat) : Nat := List.countP isPrime (List.range (n + 1))

end Submission
