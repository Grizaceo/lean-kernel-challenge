import Spec
import Submission

/-! Lemma A, step 1: the index/length auxiliaries.

Everything the recurrence needs, stated over `Submission.nthNat` (the candidate's own
accessor) rather than `getD`, so the induction hypotheses line up with what the
row update actually produces.

`off` (the block offset) deliberately does NOT appear: the predecessor of
position `m` is `prev[m]` when `m < d` and `out[m-d]` otherwise, and that is
offset-free. That is what makes a single strong induction on `m` close.
-/

namespace Probe

open List

theorem nthNat_getD (t : List Nat) (m : Nat) : Submission.nthNat t m = t.getD m 0 := by
  induction t generalizing m with
  | nil => rfl
  | cons x xs ih =>
    cases m with
    | zero => rfl
    | succ m => simp [Submission.nthNat, ih]

theorem nthNat_append (a b : List Nat) (m : Nat) :
    Submission.nthNat (a ++ b) m
      = if m < a.length then Submission.nthNat a m else Submission.nthNat b (m - a.length) := by
  induction a generalizing m with
  | nil => simp [Submission.nthNat]
  | cons x xs ih =>
    cases m with
    | zero => simp [Submission.nthNat]
    | succ m => simp [Submission.nthNat, ih, Nat.succ_lt_succ_iff]

theorem nthNat_addBlocks : ∀ (a b : List Nat) (m : Nat),
    m < a.length → m < b.length →
    Submission.nthNat (Submission.addBlocks a b) m = Submission.nthNat a m + Submission.nthNat b m := by
  intro a
  induction a with
  | nil =>
    intro b m h₁
    simp at h₁
  | cons x xs ih =>
    intro b m h₁ h₂
    cases m with
    | zero =>
      cases b with
      | nil => simp at h₂
      | cons y ys => simp [Submission.addBlocks, Submission.nthNat]
    | succ m =>
      have h₁' : m < xs.length := by
        simp only [List.length_cons] at h₁; omega
      cases b with
      | nil => simp at h₂
      | cons y ys =>
        have h₂'' : m < ys.length := by
          simp only [List.length_cons] at h₂; omega
        show Submission.nthNat ((x + y) :: Submission.addBlocks xs ys) (m + 1)
            = Submission.nthNat xs m + Submission.nthNat (y :: ys) (m + 1)
        simp only [Submission.nthNat]
        exact ih ys m h₁' h₂''

/-- `Submission.addBlocks` truncates to the shorter side. -/
theorem length_addBlocks (a b : List Nat) :
    (Submission.addBlocks a b).length = min a.length b.length := by
  induction a generalizing b with
  | nil => simp [Submission.addBlocks]
  | cons x xs ih =>
    cases b with
    | nil => simp [Submission.addBlocks]
    | cons y ys => simp [Submission.addBlocks, ih, List.length_cons]

/-- `take` and `drop` transport `Submission.nthNat` in the two directions the block split
needs. -/
theorem nthNat_take (t : List Nat) (d m : Nat) (h₁ : m < t.length) (h₂ : m < d) :
    Submission.nthNat (t.take d) m = Submission.nthNat t m := by
  induction t generalizing d m with
  | nil => simp at h₁
  | cons x xs ih =>
    cases d with
    | zero => simp at h₂
    | succ d =>
      cases m with
      | zero => rfl
      | succ m =>
        have e₁ : m < xs.length := by
          simp only [List.length_cons] at h₁; omega
        have e₂ : m < d := by
          simp only [Nat.lt_succ_iff] at h₂; omega
        show Submission.nthNat (xs.take d) m = Submission.nthNat xs m
        exact ih d m e₁ e₂

/-- `drop` transports `Submission.nthNat` by exactly the dropped count.

`Submission.nthNat` recurses on its index while `List.drop` recurses on the list, so the
two do not line up: the induction hypothesis must be applied at index `m+1`
(not `m`), and the hypothesis likewise. Inducting on `t` with `d` and `m`
generalized gives the IH at every index, which is what closes both cases. -/
theorem nthNat_drop (t : List Nat) (d m : Nat) (h : m < (t.drop d).length) :
    Submission.nthNat (t.drop d) m = Submission.nthNat t (m + d) := by
  induction t generalizing d m with
  | nil => simp at h
  | cons x xs ih =>
    cases d with
    | zero => rfl
    | succ d =>
      have h' : m < (xs.drop d).length := by simpa using h
      cases m with
      | zero =>
        show Submission.nthNat (xs.drop d) 0 = Submission.nthNat (x :: xs) (0 + (d + 1))
        have hnorm : 0 + (d + 1) = d + 1 := by omega
        rw [hnorm]
        -- peel the cons: `Submission.nthNat (x :: xs) (d+1)` reduces to `Submission.nthNat xs d`
        rw [show Submission.nthNat (x :: xs) (d + 1) = Submission.nthNat xs d from rfl]
        -- `0 + d = d` is a Nat fact, but `omega` cannot close it here because the
        -- goal mentions `Submission.nthNat` (opaque to the arithmetical solver). Give it the
        -- normalization as an explicit equation instead.
        have hz : Submission.nthNat xs (0 + d) = Submission.nthNat xs d := by
          rw [show (0 + d) = d from by omega]
        exact (ih d 0 h').trans hz
      | succ m =>
        show Submission.nthNat (xs.drop d) (m + 1) = Submission.nthNat (x :: xs) ((m + 1) + (d + 1))
        have hnorm : (m + 1) + (d + 1) = (m + 1) + d + 1 := by omega
        rw [hnorm]
        rw [show Submission.nthNat (x :: xs) (m + 1 + d + 1) = Submission.nthNat xs (m + 1 + d) from rfl]
        exact ih d (m + 1) h'

/-- **Lemma A**, the one new obligation for `partition-stream-addblocks`.

The block update satisfies the same single-part recurrence the Spec sums over:

    out[m] = t[m] + (if d ≤ m then out[m-d] else 0)

The proof is via the generalized form `lemmaA_gen` below, in which `zipBlocksAdd`
is generalized over its `prev` block: after one block the predecessor is the
*new* block, not zeros, so a statement pinned to `p = replicate d 0` cannot be
re-applied at the next block. The block offset is deliberately absent from both
statements — the predecessor of `m` is `prev[m]` when `m < d` and `out[m-d]`
otherwise — so a single strong induction on `m` closes, with no index
arithmetic.

`chunks` and `zipBlocksAdd` are defined with an explicit fuel argument rather
than `termination_by`; the fuel is what makes them structurally recursive, and
the induction steps through it.

`zipBlocksAdd` must be generalized over its `prev` block `p`: after one block
the predecessor is the *new* block, not zeros, so a statement pinned to
`p = replicate d 0` cannot be re-applied at the next block.

`l.length ≤ fuel` is the "enough blocks" invariant, and it is what makes the
fuel argument legal in the recursive call. `0 < fuel` alone would NOT: with
`fuel = 0` the chunk list is empty while `l` is not, and the claim is simply
false. The candidate satisfies it with equality (`fuel := t.length`).

Statement shape, and why it closes:

  * `m < d` — the position is inside the FIRST block, so it is
    `blk[m] + p[m]`: the `else` branch `p[m]` is exactly right.
  * `m ≥ d` — `nthNat_append` gives `out[m] = tail[m-d]`, and the induction
    hypothesis at `m-d` (strictly smaller, hence needing `0 < d`) gives
    `tail[m-d] = l[m] + (if d ≤ m-d then tail[m-2d] else bn[m-d])`.
    Re-reading that bracket through `nthNat_append` on `out` at `m-d` shows it
    is precisely `out[m-d]`, so the goal closes with no index arithmetic.

`Nat.strongRecOn` is the core strong-induction eliminator; `Nat.strongRecOn` is
`noncomputable`, which is harmless here because this is a `Prop` and does not
touch the candidate's `impl`. -/
theorem lemmaA_gen : ∀ (d m : Nat) (p : List Nat) (fuel : Nat) (l : List Nat),
    0 < d → p.length = d → l.length ≤ fuel → m < l.length →
    Submission.nthNat (Submission.zipBlocksAdd p (Submission.chunks d fuel l)) m
      = Submission.nthNat l m
        + (if d ≤ m
           then Submission.nthNat
                  (Submission.zipBlocksAdd p (Submission.chunks d fuel l)) (m - d)
           else Submission.nthNat p m) := by
  intro d m
  induction m using Nat.strongRecOn with
  | _ m ih =>
    intro p fuel l hd hp hfuel hml
    -- `chunks` peels one block per unit of fuel
    cases hfuel' : fuel with
    | zero =>
      -- fuel = 0 makes the chunk list empty, so `out = []` and `out[m] = 0`.
      -- The goal then needs `l[m] + (if ...) = 0`, which is NOT provable, so
      -- this branch must be excluded: `l.length ≤ 0` forces `l = []`, and
      -- `m < l.length` is then absurd.
      subst hfuel'
      have : l = [] := by
        cases l with
        | nil => rfl
        | cons x xs => simp at hfuel
      subst this
      simp at hml
    | succ fuel =>
      subst hfuel'
      cases l with
      | nil => simp at hml
      | cons x xs =>
        -- one block peeled: blk = (x::xs).take d, rest = chunks d fuel (drop d)
        have hchunks : Submission.chunks d (Nat.succ fuel) (x :: xs)
            = (x :: xs).take d :: Submission.chunks d fuel ((x :: xs).drop d) := rfl
        have hzip : Submission.zipBlocksAdd p
              ((x :: xs).take d :: Submission.chunks d fuel ((x :: xs).drop d))
            = Submission.addBlocks ((x :: xs).take d) p
              ++ Submission.zipBlocksAdd
                   (Submission.addBlocks ((x :: xs).take d) p)
                   (Submission.chunks d fuel ((x :: xs).drop d)) := rfl
        -- Let `blk` be the peeled first block and `bn` the new block. Core Lean
        -- 4.33 has neither `set ... with` nor a usable `let`-form for `simp`,
        -- so the terms are written out in full throughout.
        --
        -- `blk` is `min d l.length` long and `p` is `d` long, so `bn` is
        -- `min d l.length` long. The proof splits on whether `m` lands inside
        -- the first block.
        have hblk_len : ((x :: xs).take d).length = min d (x :: xs).length := by
          simp [List.length_take]
        have hbn_len : (Submission.addBlocks ((x :: xs).take d) p).length
            = min ((x :: xs).take d).length p.length := by
          simp [length_addBlocks]
        -- reduce the goal to the peeled form
        show Submission.nthNat
              (Submission.addBlocks ((x :: xs).take d) p
                ++ Submission.zipBlocksAdd
                     (Submission.addBlocks ((x :: xs).take d) p)
                     (Submission.chunks d fuel ((x :: xs).drop d))) m
            = Submission.nthNat (x :: xs) m
              + (if d ≤ m
                 then Submission.nthNat
                        (Submission.addBlocks ((x :: xs).take d) p
                          ++ Submission.zipBlocksAdd
                               (Submission.addBlocks ((x :: xs).take d) p)
                               (Submission.chunks d fuel ((x :: xs).drop d))) (m - d)
                 else Submission.nthNat p m)
        -- `m < d`: the position is in the first block, so the `else` branch
        -- `p[m]` is exactly the second addend.
        by_cases hmd : m < d
        · have hmin : m < min d (x :: xs).length := by omega
          rw [nthNat_append]
          -- fold the length through `min` so the guard is `m < d`
          rw [hbn_len, hp, hblk_len]
          have hminmin : min (min d (x :: xs).length) d = min d (x :: xs).length := by
            omega
          rw [hminmin, if_pos hmin]
          -- `bn[m] = blk[m] + p[m]`
          have hbnm : Submission.nthNat (Submission.addBlocks ((x :: xs).take d) p) m
              = Submission.nthNat ((x :: xs).take d) m + Submission.nthNat p m := by
            apply nthNat_addBlocks ((x :: xs).take d) p m
            · rw [hblk_len]; exact hmin
            · rw [hp]; exact hmd
          -- and `blk[m] = (x :: xs)[m]` since `m < d`
          have hblkm : Submission.nthNat ((x :: xs).take d) m
              = Submission.nthNat (x :: xs) m := by
            exact nthNat_take (x :: xs) d m (by omega) hmd
          rw [hbnm, hblkm]
          have hdnot : ¬ (d ≤ m) := by omega
          rw [if_neg hdnot]
        · -- `m ≥ d`: the position is past the first block, so
          -- `out[m] = tail[m-d]`, and the induction hypothesis at `m-d`
          -- (strictly smaller because `0 < d`) gives
          -- `tail[m-d] = l[m] + (if d ≤ m-d then tail[m-2d] else bn[m-d])`.
          -- Re-reading that bracket through `nthNat_append` on `out` at `m-d`
          -- shows it is exactly `out[m-d]`, so the goal closes with no index
          -- arithmetic.
          have hdlt : d ≤ m := by omega
          have hdl : d ≤ (x :: xs).length := by omega
          rw [nthNat_append]
          rw [hbn_len, hp, hblk_len]
          have hminmin : min (min d (x :: xs).length) d = d := by
            have hdl' : d ≤ xs.length + 1 := by simpa using hdl
            simp only [List.length_cons]; omega
          rw [hminmin]
          have hnotmin : ¬ (m < d) := by omega
          rw [if_neg hnotmin]
          -- LHS is now `tail[m - d]`, and this is exactly the statement the
          -- induction hypothesis proves for the shorter index `m - d`.
          have hmd_lt : m - d < m := by omega
          -- NOTE: no `let` for `bn`/`tail`. Core Lean 4.33 will not unify
          -- `nthNat_drop`'s conclusion through a `let`-bound abbreviation
          -- (`apply` fails with "could not unify"), so the terms are written
          -- out in full. The lengths are pinned first instead.
          have hmin_d : min d (x :: xs).length = d := by
            have hdl' : d ≤ xs.length + 1 := by simpa using hdl
            simp only [List.length_cons]; omega
          have hbn_len' : (Submission.addBlocks ((x :: xs).take d) p).length = d := by
            rw [length_addBlocks, hblk_len, hp, hmin_d]
            exact Nat.min_self _
          have hdrop_len : ((x :: xs).drop d).length = (x :: xs).length - d := by
            simp [List.length_drop]
          have hfuel' : ((x :: xs).drop d).length ≤ fuel := by
            have hfuel' : (xs.length + 1) - d ≤ fuel := by
              simp only [List.length_cons] at hfuel ⊢; omega
            rw [hdrop_len, List.length_cons]
            omega
          have hml' : m - d < ((x :: xs).drop d).length := by
            have hml' : m - d < (xs.length + 1) - d := by
              simp only [List.length_cons] at hml ⊢; omega
            rw [hdrop_len, List.length_cons]
            omega
          -- `nthNat_drop` concludes at `m + d`, so re-index: `(m-d) + d = m`
          have hstep : Submission.nthNat ((x :: xs).drop d) (m - d)
              = Submission.nthNat (x :: xs) m := by
            rw [nthNat_drop (x :: xs) d (m - d) hml']
            congr 1
            omega
          -- the induction hypothesis, instantiated one block in
          have e := ih (m - d) hmd_lt
              (Submission.addBlocks ((x :: xs).take d) p) fuel ((x :: xs).drop d)
              hd hbn_len' hfuel' hml'
          rw [hstep] at e
          -- the goal's bracket, with `d ≤ m` discharged, is `nthNat (bn ++ tail) (m-d)`
          have hbracket : (if d ≤ m
                  then Submission.nthNat
                       (Submission.addBlocks ((x :: xs).take d) p
                         ++ Submission.zipBlocksAdd
                              (Submission.addBlocks ((x :: xs).take d) p)
                              (Submission.chunks d fuel ((x :: xs).drop d))) (m - d)
                  else Submission.nthNat p m)
              = Submission.nthNat
                  (Submission.addBlocks ((x :: xs).take d) p
                    ++ Submission.zipBlocksAdd
                         (Submission.addBlocks ((x :: xs).take d) p)
                         (Submission.chunks d fuel ((x :: xs).drop d))) (m - d) := by
            rw [if_pos hdlt]
          -- and the IH's bracket is the same thing, read through `nthNat_append`
          have hbracket' : (if d ≤ m - d
                  then Submission.nthNat
                       (Submission.zipBlocksAdd
                         (Submission.addBlocks ((x :: xs).take d) p)
                         (Submission.chunks d fuel ((x :: xs).drop d))) (m - d - d)
                  else Submission.nthNat
                       (Submission.addBlocks ((x :: xs).take d) p) (m - d))
              = Submission.nthNat
                  (Submission.addBlocks ((x :: xs).take d) p
                    ++ Submission.zipBlocksAdd
                         (Submission.addBlocks ((x :: xs).take d) p)
                         (Submission.chunks d fuel ((x :: xs).drop d))) (m - d) := by
            by_cases h : m - d < d
            · rw [nthNat_append, hbn_len', if_pos h, if_neg (by omega)]
            · rw [nthNat_append, hbn_len', if_neg h, if_pos (by omega),
                  show m - d - d = (m - d) - d by omega]
          rw [hbracket'] at e
          rw [hbracket]
          exact e

/-- Every entry of `replicate d 0` is zero, so `nthNat` of it is zero. Proved by
induction rather than via `getD`/`getElem?` bridging: `List.getD_eq_getElem?`
and `List.getD_eq_default` do not exist in this toolchain's `Init`, and the
`getElem?` spelling does not reduce under `simp` either. -/
theorem nthNat_replicate_zero (d m : Nat) :
    Submission.nthNat (List.replicate d 0) m = 0 := by
  induction d generalizing m with
  | zero => rfl
  | succ d ih =>
    cases m with
    | zero => rfl
    | succ m =>
      show Submission.nthNat (List.replicate d 0) m = 0
      exact ih m

/-- **Lemma A**, specialized: the candidate's row update satisfies the same
single-part recurrence the Spec sums over.

    out[m] = t[m] + (if d ≤ m then out[m-d] else 0)

The `else 0` comes from `p = List.replicate d 0`, whose entries are all zero.
The hypotheses hold at the call site: `0 < d` because part sizes run `k + 1`,
`p.length = d` because `replicate d 0` has length `d`, and
`l.length ≤ fuel` with equality because the candidate passes `fuel := t.length`. -/
theorem lemmaA (d : Nat) (t : List Nat) (m : Nat)
    (hd : 0 < d) (h₀ : m < t.length) :
    Submission.nthNat (Submission.updRowAdd d t) m
      = Submission.nthNat t m
        + (if d ≤ m then Submission.nthNat (Submission.updRowAdd d t) (m - d)
           else 0) := by
  have hp : (List.replicate d 0).length = d := by simp
  have hfuel : t.length ≤ t.length := Nat.le_refl t.length
  have h := lemmaA_gen d m (List.replicate d 0) t.length t hd hp hfuel h₀
  show Submission.nthNat
      (Submission.zipBlocksAdd (List.replicate d 0)
        (Submission.chunks d t.length t)) m = _
  rw [h, nthNat_replicate_zero]
  split <;> rename_i hcond
  · rfl
  · rfl

end Probe
