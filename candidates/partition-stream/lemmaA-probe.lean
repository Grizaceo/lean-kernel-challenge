import Spec

/-! Lemma A probe, part 1: the list-indexing plumbing.

Everything the block induction needs reduces to these four facts about `nthNat`
and `List.zipWith`, in core Lean with no Mathlib. If these compile, the block
induction is a matter of bookkeeping; if they do not, Lemma A is not reachable
and `partition-stream` is a ceiling.
-/

namespace Probe

open List

/-- Copied verbatim from the candidate: element `i` of `xs`, or 0 past the end. -/
def nthNat : List Nat → Nat → Nat
  | [], _ => 0
  | x :: _, 0 => x
  | _ :: xs, i + 1 => nthNat xs i

theorem nthNat_getD (t : List Nat) (m : Nat) : nthNat t m = t.getD m 0 := by
  induction t generalizing m with
  | nil => rfl
  | cons x xs ih =>
    cases m with
    | zero => rfl
    | succ m => simp [nthNat, List.getD_cons_succ, ih]

/-- How `nthNat` splits across an append. This is the workhorse: every step of
the block induction is a re-association through this equation. -/
theorem nthNat_append (a b : List Nat) (m : Nat) :
    nthNat (a ++ b) m
      = if m < a.length then nthNat a m else nthNat b (m - a.length) := by
  induction a generalizing m with
  | nil => simp [nthNat]
  | cons x xs ih =>
    cases m with
    | zero => simp [nthNat]
    | succ m => simp [nthNat, ih, Nat.succ_lt_succ_iff]

/-- `nthNat` through a structural elementwise add, wherever both sides are
defined.

Why not `List.zipWith` (which the measured candidate uses)? In this toolchain
`List.zipWith` is `zipWithTR`, which accumulates into an `Array` and exposes NO
`cons` equation — there is no `zipWith_cons_cons` in core's `Init`, and
`grep` over the toolchain's `Init/Data/List` finds no equation lemmas for it at
all. So the block induction has nothing to `simp` with and the lemma is not
provable by structural induction on the shipped candidate. `addBlocks` is the
same truncation, recursing structurally, and it does have `simp` equations.

Induction is on `a` with `b` ALSO generalized, because `addBlocks` consumes one
element of each side per step; the IH must be available for every tail of `b`,
not only the original one. -/
def addBlocks : List Nat → List Nat → List Nat
  | a :: as, b :: bs => (a + b) :: addBlocks as bs
  | _, _ => []

theorem nthNat_addBlocks : ∀ (a b : List Nat) (m : Nat),
    m < a.length → m < b.length →
    nthNat (addBlocks a b) m = nthNat a m + nthNat b m := by
  intro a
  induction a with
  | nil =>
    intro b m h₁
    simp at h₁
  | cons x xs ih =>
    intro b m h₁ h₂
    cases m with
    | zero =>
      -- head case: `addBlocks` conses when both sides are nonempty
      cases b with
      | nil => simp at h₂
      | cons y ys => simp [addBlocks, nthNat]
    | succ m =>
      have h₁' : m < xs.length := by
        simp only [List.length_cons] at h₁; omega
      cases b with
      | nil => simp at h₂
      | cons y ys =>
        have h₁' : m < xs.length := by
          simp only [List.length_cons] at h₁; omega
        have h₂'' : m < ys.length := by
          simp only [List.length_cons] at h₂; omega
        show nthNat ((x + y) :: addBlocks xs ys) (m + 1)
            = nthNat xs m + nthNat (y :: ys) (m + 1)
        simp only [nthNat]
        exact ih ys m h₁' h₂''

end Probe
