import Spec

/-!
Integer partitions via block-streaming rows.

`impl n` runs the reference recurrence `partAux n n` as `n` row updates over a
materialized table, one row per part size, rather than re-reducing the whole
closure at every cell.

The row update is `updRowAdd d t`, which is streaming: it chunks `t` into
blocks of size `d` and folds `zipBlocksAdd` over them, so each cell is touched
once instead of `d` times. Correctness rests on three identifications:

  1. `nthNat (updRowAdd d t) m` is, on columns `m < t.length`, exactly the
     reference step `T d` on the column-reading function;
  2. the reference recurrence `partAux (k+1) m` *is* `T (k+1) (partAux k) m`,
     definitionally, since both are the same `msum`;
  3. the row-step operators commute, so `itAdd k` -- which applies the sizes in
     *decreasing* order -- computes the same operator as the *increasing* order
     `partAux` uses.

Point 3 is the only place the iteration order is reconciled, and it is where the
streaming implementation is allowed to differ from the spec's shape.

`impl_correct` depends on no axioms beyond Lean's own `propext` and
`Quot.sound`.

The proof scaffolding is inlined below because the submission is a single file;
the same content lives in `Part.lean` and its dependencies in the working tree.
`Len.lean` and `Part.lean` share one namespace here, since each references
declarations of the other.
-/

-- In the single-file layout `Submission.nthNat` is defined above rather than
-- imported, so a few `simp [Submission.nthNat]` arguments become redundant and
-- the unused-simp-argument linter fires under `warningAsError`. The unfolding
-- those tactics rely on still happens.
set_option linter.unusedSimpArgs false

namespace Submission

def nthNat : List Nat → Nat → Nat
  | [], _ => 0
  | x :: _, 0 => x
  | _ :: xs, i + 1 => nthNat xs i

def chunks (d : Nat) : Nat → List Nat → List (List Nat)
  | 0, _ => []
  | _ + 1, [] => []
  | fuel + 1, l => l.take d :: chunks d fuel (l.drop d)

def addBlocks : List Nat → List Nat → List Nat
  | a :: as, b :: bs => (a + b) :: addBlocks as bs
  | _, _ => []

def zipBlocksAdd : List Nat → List (List Nat) → List Nat
  | _, [] => []
  | prev, blk :: rest =>
    let bn := addBlocks blk prev
    bn ++ zipBlocksAdd bn rest

def updRowAdd (d : Nat) (t : List Nat) : List Nat :=
  zipBlocksAdd (List.replicate d 0) (chunks d t.length t)

def initTable (n : Nat) : List Nat := 1 :: List.replicate n 0

def itAdd : Nat → List Nat → List Nat
  | 0, t => t
  | k + 1, t => itAdd k (updRowAdd (k + 1) t)

def impl (n : Nat) : Nat := nthNat (itAdd n (initTable n)) n

end Submission


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



/-- Every block produced by `chunks` is at most `d` long. -/
theorem chunks_blocks_le (d : Nat) : ∀ (fuel : Nat) (l : List Nat) (b : List Nat),
    b ∈ Submission.chunks d fuel l → b.length ≤ d := by
  intro fuel
  induction fuel with
  | zero => intro l b h; cases h
  | succ fuel ih =>
    intro l b h
    have hnil : Submission.chunks d (fuel+1) ([] : List Nat) = [] := rfl
    cases l with
    | nil =>
        rw [hnil] at h
        cases h
    | cons a l =>
      rw [show Submission.chunks d (fuel+1) (a :: l)
             = (a :: l).take d :: Submission.chunks d fuel ((a :: l).drop d) from rfl] at h
      simp only [List.mem_cons] at h
      cases h with
      | inl heq =>
        cases heq
        have hlen : (List.take d (a :: l)).length = min d (l.length + 1) := by
          simp [List.length_take]
        rw [hlen]
        exact Nat.min_le_left _ _
      | inr hrest => exact ih ((a :: l).drop d) b hrest

/-- The total block count produced by `chunks d fuel l`. -/
def sumLen : List (List Nat) → Nat
  | [] => 0
  | b :: rest => b.length + sumLen rest

theorem sumLen_chunks_nil (d fuel : Nat) :
    sumLen (Submission.chunks d (fuel+1) ([] : List Nat)) = min (d * (fuel+1)) 0 := by
  have h1 : (Submission.chunks d (fuel+1) ([] : List Nat)) = [] := rfl
  rw [h1, sumLen, Nat.min_eq_right (Nat.zero_le _)]

theorem sumLen_chunks_cons (d fuel : Nat) (a : Nat) (l : List Nat)
    (ih : ∀ (m : List Nat), sumLen (Submission.chunks d fuel m) = min (d * fuel) m.length) :
    sumLen (Submission.chunks d (fuel+1) (a :: l)) = min (d * (fuel+1)) (l.length + 1) := by
  have hdrop : ((a :: l).drop d).length = l.length + 1 - d := by
    cases d with
    | zero => simp
    | succ d => simp
  have htake : ((a :: l).take d).length = min d (l.length + 1) := by
    cases d with
    | zero => simp
    | succ d => simp
  have hchunks : Submission.chunks d (fuel+1) (a :: l)
      = (a :: l).take d :: Submission.chunks d fuel ((a :: l).drop d) := rfl
  rw [hchunks, sumLen, htake, ih, hdrop]
  by_cases hd0 : d = 0
  · rw [hd0]
    have h1 : min 0 (l.length + 1) = 0 := Nat.min_eq_left (Nat.zero_le _)
    have h2 : min (0 * fuel) (l.length + 1 - 0) = 0 := by
      rw [Nat.zero_mul, Nat.sub_zero, Nat.min_eq_left (Nat.zero_le _)]
    have h3 : min (0 * (fuel + 1)) (l.length + 1) = 0 := by
      rw [Nat.zero_mul, Nat.min_eq_left (Nat.zero_le _)]
    rw [h1, h2, h3]
  · by_cases hle : d ≤ l.length + 1
    · by_cases hdf : d * fuel ≤ l.length + 1 - d
      · rw [Nat.min_eq_left hle, Nat.min_eq_left hdf, Nat.mul_add, Nat.mul_one,
            Nat.add_comm, Nat.min_eq_left (by omega)]
      · have hc : l.length + 1 - d + d = l.length + 1 := Nat.sub_add_cancel hle
        rw [Nat.min_eq_left hle, Nat.min_eq_right (by omega), Nat.mul_add,
            Nat.mul_one, Nat.add_comm, hc, Nat.min_eq_right (by omega)]
    · have hm : d * (fuel + 1) = d * fuel + d := by
        rw [Nat.mul_add, Nat.mul_one]
      rw [hm, Nat.min_eq_right (Nat.le_of_not_ge hle)]
      have hz : l.length + 1 - d = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_not_ge hle)
      have hmf : min (d * fuel) (l.length + 1 - d) = 0 := by
        rw [hz, Nat.min_eq_right (Nat.zero_le _)]
      rw [hmf, Nat.add_zero, Nat.min_eq_right (by omega)]

theorem sumLen_chunks (d : Nat) : ∀ (fuel : Nat) (l : List Nat),
    sumLen (Submission.chunks d fuel l) = min (d * fuel) l.length := by
  intro fuel
  induction fuel with
  | zero => intro l; simp [Submission.chunks, sumLen, Nat.mul_zero, Nat.min_eq_left]
  | succ fuel ih =>
    intro l
    cases l with
    | nil => exact sumLen_chunks_nil d fuel
    | cons a l =>
      rw [show (a :: l).length = l.length + 1 from rfl]
      rw [sumLen_chunks_cons d fuel a l ih]



/-- **The bridge lemma.** The candidate's tabled row update obeys precisely the
reference recurrence `upd f k m = f m + (if k+1 ≤ m then upd f k (m-(k+1)) else 0)`,
read off the materialized lists via `nthNat`.

This is `LemmaA.lemmaA` instantiated at `d := k + 1`. -/
theorem nthNat_updRowAdd (t : List Nat) (k m : Nat) (hm : m < t.length) :
    Submission.nthNat (Submission.updRowAdd (k + 1) t) m
      = (if k + 1 ≤ m
         then Submission.nthNat t m
                + Submission.nthNat (Submission.updRowAdd (k + 1) t) (m - (k + 1))
         else Submission.nthNat t m) := by
  have h := lemmaA (k + 1) t m (Nat.succ_pos k) hm
  by_cases hle : k + 1 ≤ m
  · rw [if_pos hle] at h
    rw [if_pos hle, h]
  · rw [if_neg hle] at h
    rw [if_neg hle, h]
    exact Nat.add_zero _



/-! ## Transport: `nthNat` reads like `getD` -/

/-- `nthNat` is `getD` with default `0`. -/
theorem nthNat_eq_getD : ∀ (t : List Nat) (m : Nat), Submission.nthNat t m = t.getD m 0 := by
  intro t
  induction t with
  | nil => intro m; cases m <;> rfl
  | cons x xs ih =>
    intro m
    cases m with
    | zero => rfl
    | succ m => exact ih m



/-! ## The msum scaffolding -/

def msum (f : Nat → Nat) (M : Nat) : Nat :=
  (List.range M).map f |>.foldl (· + ·) 0

theorem msum_succ (f : Nat → Nat) (M : Nat) :
    msum f (M + 1) = msum f M + f M := by
  unfold msum
  rw [List.range_succ, List.map_append, List.foldl_append]
  rfl

theorem msum_congr {f g : Nat → Nat} (M : Nat) (h : ∀ j, j < M → f j = g j) :
    msum f M = msum g M := by
  induction M with
  | zero => rfl
  | succ M ih =>
    rw [msum_succ, msum_succ, h M (Nat.lt_succ_self M)]
    rw [ih (fun j hj => h j (Nat.lt_trans hj (Nat.lt_succ_self M)))]

theorem msum_zero (f : Nat → Nat) : msum f 0 = 0 := rfl

theorem msum_peel (f : Nat → Nat) (d : Nat) :
    ∀ m M, msum (fun j => f (m - j * d)) (M + 1)
         = f m + msum (fun i => f (m - (i + 1) * d)) M := by
  intro m M
  induction M with
  | zero =>
    rw [Nat.zero_add]
    show msum (fun j => f (m - j * d)) 1 = f m + msum (fun i => f (m - (i + 1) * d)) 0
    rw [msum_succ]
    show msum (fun j => f (m - j * d)) 0 + f (m - 0 * d)
      = f m + msum (fun i => f (m - (i + 1) * d)) 0
    rw [show msum (fun j => f (m - j * d)) 0 = 0 from msum_zero (fun j => f (m - j * d)),
        show msum (fun i => f (m - (i + 1) * d)) 0 = 0 from msum_zero (fun i => f (m - (i + 1) * d)),
        Nat.zero_mul, Nat.zero_add, Nat.add_zero, Nat.sub_zero]
  | succ M ih =>
    show msum (fun j => f (m - j * d)) (M + 1 + 1)
      = f m + msum (fun i => f (m - (i + 1) * d)) (M + 1)
    rw [show M + 1 + 1 = Nat.succ (Nat.succ M) from rfl]
    rw [msum_succ, ih, msum_succ, Nat.add_assoc]



/-! ## The reference characterisation, on `nthNat` rows -/

/-- Shift identity for truncated subtraction:
`(m - d) - j*d = m - (j+1)*d`. -/
theorem sub_sub_eq (m d j : Nat) : (m - d) - j * d = m - (j + 1) * d := by
  rw [Nat.sub_sub, Nat.add_mul, Nat.one_mul, Nat.add_comm d (j * d)]

/-- The reference recurrence over a column function, mirroring `Submission.upd`
from the foldl candidate: `k` counts already-accepted part sizes, so the new
part size is `k + 1`. -/
def updRef (f : Nat → Nat) (k : Nat) : Nat → Nat
  | m => if k + 1 ≤ m then f m + updRef f k (m - (k + 1)) else f m
termination_by m => m
decreasing_by
  rename_i h
  exact Nat.sub_lt (Nat.lt_of_lt_of_le (Nat.succ_pos k) h) (Nat.succ_pos k)

/-- Unrolling `updRef`: it is the sum over multiplicities `j` of part size
`d = k+1`, exactly the spec's `map`+`foldl` shape. -/
theorem updRef_eq_msum (f : Nat → Nat) (d : Nat) (hd : 0 < d) :
    ∀ k m, k + 1 = d → updRef f k m = msum (fun j => f (m - j * d)) (m / d + 1) := by
  intro k m hkd
  induction m using Nat.strongRecOn with
  | _ m ih =>
    by_cases h : k + 1 ≤ m
    · unfold updRef
      rw [if_pos h]
      rw [← hkd]
      generalize hm' : m - (k + 1) = m'
      have hmEq : m = m' + (k + 1) := by
        rw [← hm']
        exact (Nat.sub_add_cancel h).symm
      have hlt : m' < m := by
        rw [← hm']
        exact Nat.sub_lt (Nat.lt_of_lt_of_le (Nat.succ_pos k) h) (Nat.succ_pos k)
      have ih' := ih m' hlt
      have hdiv : m / (k + 1) = m' / (k + 1) + 1 := by
        have this : m' + (k + 1) - (k + 1) = m' := Nat.add_sub_cancel m' (k + 1)
        rw [hmEq, Nat.div_eq, if_pos ⟨hkd ▸ hd, Nat.le_add_left (k + 1) m'⟩, this]
      rw [hdiv, msum_succ, msum_peel, ih', Nat.add_comm]
      -- re-index the peeled sum back onto the predecessor row
      have cong : msum (fun i => f (m - (i + 1) * (k + 1))) (m' / (k + 1))
                = msum (fun i => f (m' - i * d)) (m' / d) := by
        rw [← hkd]
        apply msum_congr
        intro i _
        congr 1
        rw [← hm', sub_sub_eq m (k + 1) i]
      rw [cong]
      -- the residual `f m` is the `j = 0` term, which `hmEq` re-expresses
      have hlast : m - (m' / (k + 1) + 1) * (k + 1) = m' - (m' / (k + 1)) * (k + 1) := by
        rw [hmEq, Nat.add_mul, Nat.one_mul]
        omega
      rw [hlast, ← hkd, msum_succ]
      simp [Nat.add_comm, Nat.add_left_comm]
    · unfold updRef
      rw [if_neg h]
      rw [← hkd]
      have hdiv0 : m / (k + 1) = 0 := by
        rw [Nat.div_eq]
        exact if_neg (fun ⟨_, hle⟩ => h hle)
      rw [hdiv0, Nat.zero_add, msum_succ]
      simp [msum_zero, Nat.zero_mul]



/-! ## The row step is the reference row step -/

/-- `updRowAdd d t` reads, at column `m`, exactly the reference `upd` step on
the predecessor row.

`Bridge.nthNat_updRowAdd` gives the recurrence for the streaming row; the
reference recurrence differs only in the guard, which `d > 0` normalises via
`d - 1 + 1 = d`. Induction is on `m` because the recurrence recurses at `m - d`. -/
theorem nthNat_updRowAdd_eq_updRef (d : Nat) (hd : 0 < d) :
    ∀ (t : List Nat) (m : Nat), m < t.length →
      Submission.nthNat (Submission.updRowAdd d t) m
        = updRef (Submission.nthNat t) (d - 1) m := by
  intro t m
  induction m using Nat.strongRecOn with
  | _ m ihm =>
    intro hm
    have hrec' : Submission.nthNat (Submission.updRowAdd d t) m
        = (if d ≤ m
           then Submission.nthNat t m
                  + Submission.nthNat (Submission.updRowAdd d t) (m - d)
           else Submission.nthNat t m) := by
      have h := nthNat_updRowAdd t (d - 1) m hm
      rw [Nat.sub_add_cancel hd] at h
      exact h
    by_cases hle : d ≤ m
    · have hle' : d - 1 + 1 ≤ m := by rw [Nat.sub_add_cancel hd]; exact hle
      unfold updRef
      rw [if_pos hle', Nat.sub_add_cancel hd, hrec', if_pos hle]
      -- the recursive occurrence is the same statement at the smaller column
      have hmlt : m - d < m := Nat.sub_lt (Nat.lt_of_lt_of_le hd hle) hd
      have hinner : m - d < t.length := by omega
      exact congrArg (fun z => Submission.nthNat t m + z) (ihm (m - d) hmlt hinner)
    · have hle' : ¬ d - 1 + 1 ≤ m := by
        rw [Nat.sub_add_cancel hd]
        exact hle
      unfold updRef
      rw [if_neg hle']
      rw [hrec', if_neg hle]

/-- Consequently the streaming row step is literally the spec's `msum` over
multiplicities of part size `d`. This is the characterisation that lets the
`partition-foldl` correctness argument transfer verbatim. -/
theorem nthNat_updRowAdd_eq_msum (d : Nat) (hd : 0 < d) :
    ∀ (t : List Nat) (m : Nat), m < t.length →
      Submission.nthNat (Submission.updRowAdd d t) m
        = msum (fun j => Submission.nthNat t (m - j * d)) (m / d + 1) := by
  intro t m hm
  rw [nthNat_updRowAdd_eq_updRef d hd t m hm]
  exact updRef_eq_msum (Submission.nthNat t) d hd (d - 1) m (Nat.sub_add_cancel hd)



/-! ## The row-step operator, and why its order does not matter -/

/-- The `d`-step row operator: sum the column over multiplicities of part size
`d`. This is `updRowAdd` read column-wise. -/
def T (d : Nat) (f : Nat → Nat) : Nat → Nat :=
  fun m => msum (fun j => f (m - j * d)) (m / d + 1)

/-- A `msum` whose summands all vanish is zero. -/
theorem msum_zeros {f : Nat → Nat} {M : Nat} (h : ∀ j, j < M → f j = 0) :
    msum f M = 0 := by
  induction M with
  | zero => rfl
  | succ M ih =>
    rw [msum_succ, h M (Nat.lt_succ_self M),
      ih (fun j hj => h j (Nat.lt_trans hj (Nat.lt_succ_self M))), Nat.add_zero]

/-- `msum` distributes over addition of the summands. -/
theorem msum_add {f g : Nat → Nat} :
    ∀ (M : Nat), msum (fun i => f i + g i) M = msum f M + msum g M := by
  intro M
  induction M with
  | zero => simp [msum_zero]
  | succ M ih =>
    rw [msum_succ, msum_succ, msum_succ, ih]
    ac_rfl

/-- Swapping the order of summation over a rectangular range. Both sides sum
`g i j` over all pairs `i < K`, `j < L`, so they agree; peeling the last `j`
off the left and the last `i` off the right makes this syntactically visible. -/
theorem msum_swap (g : Nat → Nat → Nat) :
    ∀ (K L : Nat), msum (fun i => msum (fun j => g i j) L) K
        = msum (fun j => msum (fun i => g i j) K) L := by
  intro K L
  induction L with
  | zero =>
    have hz : msum (fun i => msum (fun j => g i j) 0) K = 0 := by
      have h : ∀ i, i < K → msum (fun j => g i j) 0 = 0 := by
        intro i _
        exact msum_zero _
      exact msum_zeros h
    rw [hz, msum_zero]
  | succ L ih =>
    have hdist : msum (fun i => msum (fun j => g i j) (L + 1)) K
        = msum (fun i => msum (fun j => g i j) L) K
          + msum (fun i => g i L) K := by
      calc msum (fun i => msum (fun j => g i j) (L + 1)) K
          = msum (fun i => (msum (fun j => g i j) L + g i L)) K := by
            apply msum_congr K
            intro i _
            exact msum_succ (fun j => g i j) L
        _ = _ := msum_add K
    have hinner : msum (fun j => msum (fun i => g i j) K) L + msum (fun i => g i L) K
        = msum (fun j => msum (fun i => g i j) K) (L + 1) :=
      (msum_succ (fun j => msum (fun i => g i j) K) L).symm
    rw [hdist, ih, hinner]

/-- Widening a `msum` range: indices past `M` contribute nothing, provided they
contribute nothing on the target side. -/
theorem msum_extend {f g : Nat → Nat} {M M' : Nat} (hM : M ≤ M')
    (h1 : ∀ j, j < M → f j = g j) (h2 : ∀ j, M ≤ j → j < M' → g j = 0) :
    msum f M = msum g M' := by
  induction M' generalizing M with
  | zero =>
    have hM0 : M = 0 := by omega
    subst hM0
    simp [msum_zero]
  | succ M' ih =>
    by_cases hc : M ≤ M'
    · have hlast : g M' = 0 := h2 M' (by omega) (by omega)
      have key : msum f M = msum g M' :=
        ih hc h1 (fun j hM' hlt => h2 j hM' (by omega))
      rw [msum_succ, hlast, key, Nat.add_zero]
    · have hMeq : M = M' + 1 := by omega
      have hlast : f M' = g M' := h1 M' (by omega)
      have key : msum f M' = msum g M' := msum_congr M' (fun j hj => h1 j (by omega))
      rw [hMeq, msum_succ, key, msum_succ, hlast]

/-- The triangle double sum, written so that symmetry in `a`/`b` is visible:
the guard and the argument are both symmetric, and the ranges are the natural
ones. -/
def triSum (a b m : Nat) (f : Nat → Nat) : Nat :=
  msum (fun i => msum (fun j =>
      if i * a + j * b ≤ m then f (m - i * a - j * b) else 0) (m / b + 1)) (m / a + 1)

/-- Applying the `a`-step then the `b`-step is the triangle sum. The inner range
is widened from `(m - i*a)/b + 1` to `m/b + 1`; the extra indices are exactly
those the guard rejects, so they contribute zero. -/
theorem T_seq (a b m : Nat) (hb : 0 < b) (f : Nat → Nat) :
    T a (T b f) m = triSum a b m f := by
  unfold T
  apply msum_congr
  intro i _
  -- `i` ranges over `m/a + 1`, so `i*a ≤ m`
  have hi : i * a ≤ m := Nat.mul_le_of_le_div a i m (by omega)
  have key : msum (fun j => f ((m - i * a) - j * b)) ((m - i * a) / b + 1)
      = msum (fun j => f (m - i * a - j * b)) ((m - i * a) / b + 1) := by
    refine msum_congr _ (fun j _ => ?_)
    -- (m - i*a) - j*b = m - (i*a + j*b) = m - i*a - j*b
    have h := Nat.sub_sub m (i * a) (j * b)
    rw [h]
  rw [key]
  refine msum_extend (M := (m - i * a) / b + 1) (M' := m / b + 1) ?_ ?_ ?_
  · have hsub : m - i * a ≤ m := Nat.sub_le m (i * a)
    have h : (m - i * a) / b ≤ m / b := Nat.div_le_div_right (c := b) hsub
    omega
  · intro j hj
    -- j < (m - i*a)/b + 1  ⟹  j ≤ (m - i*a)/b  ⟹  j*b ≤ m - i*a
    have hjle : j ≤ (m - i * a) / b := by omega
    have hjle' : j * b ≤ m - i * a := Nat.mul_le_of_le_div b j (m - i * a) hjle
    -- i*a + j*b ≤ i*a + (m - i*a) = m
    have htotal : i * a + j * b ≤ m := by omega
    rw [if_pos htotal]
  · intro j hj1 hj2
    -- j > (m - i*a)/b  ⟹  m - i*a < j*b, and i*a ≤ m, so i*a + j*b > m
    have hgt : (m - i * a) / b < j := by omega
    have hlt : m - i * a < j * b :=
      (Nat.div_lt_iff_lt_mul (k := b) (x := m - i * a) (y := j) hb).mp hgt
    -- i*a + j*b > i*a + (m - i*a) = m
    have hneg : ¬ i * a + j * b ≤ m := by omega
    rw [if_neg hneg]

/-- The same double sum with both ranges widened to `m + 1`. The extra indices
are exactly those the guard rejects, so the value is unchanged. With equal
ranges, symmetry in `a`/`b` is visible in the summand alone. -/
def fullSum (a b m : Nat) (f : Nat → Nat) : Nat :=
  msum (fun i => msum (fun j =>
      if i * a + j * b ≤ m then f (m - i * a - j * b) else 0) (m + 1)) (m + 1)

/-- With equal ranges, the double sum is symmetric in the two part sizes.

The symmetry is the *diagonal* one: the summand is invariant under exchanging
`(a, i)` with `(b, j)` simultaneously, and `msum_swap` lets us make that exchange
in the indices. Note that exchanging `a` and `b` at a *fixed* pair `(i, j)` is
not a symmetry — only the simultaneous exchange is. -/
theorem fullSum_comm (a b m : Nat) (f : Nat → Nat) :
    fullSum a b m f = fullSum b a m f := by
  unfold fullSum
  -- exchange the summation order
  rw [msum_swap (g := fun i j =>
      if i * a + j * b ≤ m then f (m - i * a - j * b) else 0) (K := m + 1) (L := m + 1)]
  apply msum_congr
  intro j _
  apply msum_congr
  intro i _
  -- after the swap, the two guards are `i*a + j*b ≤ m` and `j*b + i*a ≤ m`,
  -- the same inequality written in the other order
  have e : i * a + j * b = j * b + i * a := Nat.add_comm _ _
  by_cases h : i * a + j * b ≤ m
  · have h' : j * b + i * a ≤ m := by rwa [e] at h
    rw [if_pos h, if_pos h']
    -- m - i*a - j*b = m - (i*a + j*b) = m - (j*b + i*a) = m - j*b - i*a
    have e1 := Nat.sub_sub m (i * a) (j * b)
    have e2 := Nat.sub_sub m (j * b) (i * a)
    rw [e1, e2, e]
  · have h' : ¬ j * b + i * a ≤ m := by rwa [e] at h
    rw [if_neg h, if_neg h']

/-- The natural ranges are truncations of the uniform ones: an outer index past
`m/a` has `i*a > m`, and an inner index past `m/b` has `j*b > m`, so the guard
rejects them.

Both part sizes must be positive. At `b = 0` the summand does not depend on `j`
at all, while the inner range grows from `m/0 + 1 = 1` to `m + 1`, so the
widening would scale the value rather than preserve it. -/
theorem triSum_full (a b m : Nat) (ha : 0 < a) (hb : 0 < b) (f : Nat → Nat) :
    triSum a b m f = fullSum a b m f := by
  unfold triSum fullSum
  refine msum_extend (M := m / a + 1) (M' := m + 1) ?_ ?_ ?_
  · have h : m / a ≤ m := Nat.div_le_self m a
    omega
  · intro i _
    show msum (fun j => if i * a + j * b ≤ m then f (m - i * a - j * b) else 0) (m / b + 1)
        = msum (fun j => if i * a + j * b ≤ m then f (m - i * a - j * b) else 0) (m + 1)
    refine msum_extend (M := m / b + 1) (M' := m + 1) ?_ ?_ ?_
    · have h : m / b ≤ m := Nat.div_le_self m b
      omega
    · intro j _
      rfl
    · intro j hj1 hj2
      -- j > m/b  ⟹  m < j*b, so the guard can never hold
      have hgt : m / b < j := by omega
      have hlt : m < j * b :=
        (Nat.div_lt_iff_lt_mul (k := b) (x := m) (y := j) hb).mp hgt
      rw [if_neg]
      omega
  · intro i hi1 hi2
    have hlt : m < i * a := by
      have h : m / a < i := by omega
      have h' := (Nat.div_lt_iff_lt_mul (k := a) (x := m) (y := i) ha).mp h
      omega
    have hz : ∀ j, j < m + 1 →
        (if i * a + j * b ≤ m then f (m - i * a - j * b) else 0) = 0 := by
      intro j _
      have hgt : m < i * a := hlt
      rw [if_neg]
      omega
    exact msum_zeros hz

/-- The triangle sum is symmetric in the two part sizes. -/
theorem triSum_comm (a b m : Nat) (ha : 0 < a) (hb : 0 < b) (f : Nat → Nat) :
    triSum a b m f = triSum b a m f := by
  rw [triSum_full a b m ha hb f, triSum_full b a m hb ha f, fullSum_comm]

/-- The two row-step operators commute. This is what lets `itAdd` apply the part
sizes in decreasing order and still compute the same table as the spec.

The positivity of both part sizes is essential, not cosmetic: for `d = 0` the
`d`-step scales the column and does not commute with a genuine step. -/
theorem T_comm (a b : Nat) (ha : 0 < a) (hb : 0 < b) (f : Nat → Nat) :
    T a (T b f) = T b (T a f) := by
  funext m
  rw [T_seq a b m hb f, triSum_comm a b m ha hb f, T_seq b a m ha f]

/-! ## Part sizes as a list, and its order-independence -/

/-- `coin ds f m` applies the row step for every part size in `ds`, in order. -/
def coin : List Nat → (Nat → Nat) → Nat → Nat
  | [], f, m => f m
  | d :: ds, f, m => T d (coin ds f) m

theorem coin_cons (d : Nat) (ds : List Nat) (f : Nat → Nat) (m : Nat) :
    coin (d :: ds) f m = T d (coin ds f) m := rfl

/-- A step at the end of the list can be pulled to the front, by commutation. -/
theorem coin_append (ds : List Nat) (hds : ∀ y ∈ ds, 0 < y) (x : Nat) (hx : 0 < x)
    (f : Nat → Nat) : ∀ (m : Nat), coin (ds ++ [x]) f m = T x (coin ds f) m := by
  intro m
  induction ds generalizing x m with
  | nil => rfl
  | cons d ds ih =>
    have hd : 0 < d := hds d (by simp)
    have hds' : ∀ y ∈ ds, 0 < y := fun y hy => hds y (by simp [hy])
    -- peel the head of `ds ++ [x]`
    show T d (coin (ds ++ [x]) f) m = T x (T d (coin ds f)) m
    -- ih is pointwise in the column index
    have hfun : coin (ds ++ [x]) f = T x (coin ds f) := funext (ih hds' x hx)
    show T d (coin (ds ++ [x]) f) m = T x (T d (coin ds f)) m
    rw [hfun]
    -- T_comm d x : T d (T x f) = T x (T d f), which is the goal
    exact congrArg (fun g => g m) (T_comm d x hd hx (coin ds f))

/-- `coin` does not depend on the order of the part sizes: a list and its
reverse give the same count. This is what lets `itAdd` walk the part sizes
downwards while still computing the spec's table. -/
theorem coin_reverse (ds : List Nat) (hds : ∀ y ∈ ds, 0 < y) (f : Nat → Nat) :
    ∀ (m : Nat), coin ds.reverse f m = coin ds f m := by
  intro m
  induction ds generalizing m with
  | nil => rfl
  | cons a ds ih =>
    have ha : 0 < a := hds a (by simp)
    have hds' : ∀ y ∈ ds, 0 < y := fun y hy => hds y (by simp [hy])
    have hrev : ∀ y ∈ ds.reverse, 0 < y := by
      intro y hy
      rw [List.mem_reverse] at hy
      exact hds' y hy
    show coin (a :: ds).reverse f m = coin (a :: ds) f m
    rw [List.reverse_cons, coin_append ds.reverse hrev a ha f]
    show T a (coin ds.reverse f) m = T a (coin ds f) m
    unfold T
    apply msum_congr
    intro k _
    exact ih hds' (m - k * a)



/-- `(a :: l).drop d` has length `l.length + 1 - d`. -/
theorem length_drop_cons (a : Nat) (l : List Nat) (d : Nat) :
    ((a :: l).drop d).length = l.length + 1 - d := by
  cases d <;> simp

/-- `(a :: l).take d` has length `min d (l.length + 1)`. -/
theorem length_take_cons (a : Nat) (l : List Nat) (d : Nat) :
    ((a :: l).take d).length = min d (l.length + 1) := by
  cases d <;> simp

/-- A short block is terminal: the block list ends there. -/
theorem chunks_after_short (d fuel : Nat) (a : Nat) (l : List Nat)
    (hle : ¬ d ≤ l.length + 1) :
    Submission.chunks d fuel ((a :: l).drop d) = [] := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    cases hdrop_list : List.drop d (a :: l) with
    | nil => rfl
    | cons y ys =>
      have hdrop : ((a :: l).drop d).length = l.length + 1 - d :=
        length_drop_cons a l d
      have hzero : ((a :: l).drop d).length = 0 := by
        rw [hdrop]
        exact Nat.sub_eq_zero_of_le (Nat.le_of_not_ge hle)
      have hyy : (y :: ys).length = 0 := by
        rw [← hdrop_list]
        exact hzero
      simp at hyy

/-- The zipped block stream over `chunks d fuel l`, started from an accumulator
of length `d`, has `min (d * fuel) l.length` entries.

A full block keeps the accumulator at length `d`; a short block shrinks it, but
is necessarily the last one, so the shrinkage is terminal. -/
theorem length_zip_chunks : ∀ (fuel : Nat) (d : Nat) (p : List Nat) (l : List Nat),
    p.length = d →
    (Submission.zipBlocksAdd p (Submission.chunks d fuel l)).length
      = min (d * fuel) l.length := by
  intro fuel d p l hp
  induction fuel generalizing p l with
  | zero =>
    show (Submission.zipBlocksAdd p []).length = min (d * 0) l.length
    rw [Nat.mul_zero, Nat.min_eq_left (Nat.zero_le _)]
    rfl
  | succ fuel ih =>
    cases l with
    | nil =>
      show (Submission.zipBlocksAdd p []).length = min (d * (fuel + 1)) 0
      rw [Nat.min_eq_right (Nat.zero_le _)]
      rfl
    | cons a l =>
      have hunfold : Submission.chunks d (fuel + 1) (a :: l)
          = (a :: l).take d :: Submission.chunks d fuel ((a :: l).drop d) := rfl
      rw [hunfold, Submission.zipBlocksAdd, List.length_append]
      have htake : ((a :: l).take d).length = min d (l.length + 1) :=
        length_take_cons a l d
      have hlen : (a :: l).length = l.length + 1 := rfl
      by_cases hle : d ≤ l.length + 1
      · -- full block: the accumulator stays at length `d`, so `ih` applies
        have hp' : (Submission.addBlocks ((a :: l).take d) p).length = d := by
          have h := Probe.length_addBlocks ((a :: l).take d) p
          calc (Submission.addBlocks ((a :: l).take d) p).length
              = min (List.take d (a :: l)).length p.length := h
            _ = min d d := by rw [htake, hp, Nat.min_eq_left hle]
            _ = d := Nat.min_self _
        rw [ih (Submission.addBlocks ((a :: l).take d) p) ((a :: l).drop d) hp']
        rw [hp', hlen, length_drop_cons]
        by_cases h2 : d * fuel ≤ l.length + 1 - d
        · rw [Nat.min_eq_left h2, Nat.mul_succ]
          omega
        · rw [Nat.min_eq_right (Nat.le_of_not_ge h2), Nat.mul_succ]
          omega
      · -- short block: terminal, so the tail contributes nothing
        have hrest0 : Submission.chunks d fuel ((a :: l).drop d) = [] :=
          chunks_after_short d fuel a l hle
        rw [hrest0, hlen]
        -- the block itself is the whole remaining input
        have hshort : (Submission.addBlocks ((a :: l).take d) p).length = l.length + 1 := by
          have h := Probe.length_addBlocks ((a :: l).take d) p
          have h2 : min (List.take d (a :: l)).length p.length = l.length + 1 := by
            -- min (min d N) d with d ≥ N: the inner min is N, then N is the min
            have hmin : min d (l.length + 1) = l.length + 1 :=
              Nat.min_eq_right (Nat.le_of_not_ge hle)
            have hmin2 : min (l.length + 1) d = l.length + 1 := by
              rw [Nat.min_comm]
              exact hmin
            rw [htake, hp, hmin]
            exact hmin2
          exact h2 ▸ h
        rw [hshort, Submission.zipBlocksAdd]
        rw [Nat.mul_succ]
        have hN : min (d * fuel + d) (l.length + 1) = l.length + 1 := by
          have hge : l.length + 1 ≤ d * fuel + d := by
            have := hle
            omega
          exact Nat.min_eq_right hge
        rw [hN]
        omega

/-- The candidate's row update has the same length as its input. -/
theorem length_updRowAdd (d : Nat) (t : List Nat) (hd : 0 < d) :
    (Submission.updRowAdd d t).length = t.length := by
  unfold Submission.updRowAdd
  have hp : (List.replicate d 0).length = d := by simp
  rw [length_zip_chunks t.length d (List.replicate d 0) t hp]
  have hge : t.length ≤ d * t.length := by
    have hd1 : 1 ≤ d := Nat.succ_le_of_lt hd
    rw [Nat.mul_comm]
    exact Nat.le_mul_of_pos_right (n := t.length) hd1
  exact Nat.min_eq_right hge



/-- The sizes `k, k-1, …, 1`, in the order `itAdd` applies them. -/
def succRange : Nat → List Nat
  | 0 => []
  | k + 1 => (k + 1) :: succRange k

theorem succRange_succ (k : Nat) :
    succRange (k + 1) = (k + 1) :: succRange k := rfl

/-! ## Tying the streaming rows to `partAux`

`itAdd` applies the row steps in *decreasing* part size: `itAdd (k+1) t` is
`itAdd k (updRowAdd (k+1) t)`, so size `k+1` is applied first and size `1`
last. The spec's `partAux` recurrence instead wants one step per `k`, in
increasing order.

The bridge is `Coin.lean`: the row-step operators commute, so the order is
irrelevant. That lets the decreasing iteration be rewritten as the increasing
one, and `inv_step` then carries the invariant from `partAux 0` to `partAux n`.

`nthNat_updRowAdd_eq_msum` is stated for `m < t.length`, so the invariant is
carried together with the length: the table must be long enough for every
column the invariant talks about. -/

/-- `msum` is definitionally the spec's inner sum, so the streaming row step
`nthNat_updRowAdd_eq_msum` is exactly `partAux`'s unfolding. This is the
equation the whole proof is built on. -/
theorem partAux_eq_msum (k : Nat) (n : Nat) :
    partAux (k + 1) n
      = msum (fun j => partAux k (n - j * (k + 1))) (n / (k + 1) + 1) := rfl

/-- The empty partition is counted once, at every part size. -/
theorem partAux_zero (k : Nat) : partAux k 0 = 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show msum (fun j => partAux k (0 - j * (k + 1))) (0 / (k + 1) + 1) = 1
    have hz : 0 / (k + 1) = 0 := by simp
    -- the range is 0 / (k+1) + 1, so `msum_succ` peels off the single term
    rw [hz, Nat.zero_add, msum_succ, msum_zero, Nat.add_zero]
    have heq : 0 - 0 * (k + 1) = 0 := by simp
    rw [heq, ih]

/-- Column invariant after `k` row steps, stated for a *function* so it does
not depend on how the table is represented. `f` is the column-reading
function of the table; `len` is that table's length, and the invariant is
only claimed for columns below it. -/
def Inv (k : Nat) (len : Nat) (f : Nat → Nat) : Prop :=
  ∀ m, m < len → f m = if m = 0 then 1 else partAux k m

/-- The initial table satisfies the invariant for `k = 0`: every column is `0`
except column `0`, which is `1`, and `partAux 0 m = 0` for `m ≠ 0`. -/
theorem inv_init (n : Nat) :
    Inv 0 (Submission.initTable n).length
      (Submission.nthNat (Submission.initTable n)) := by
  intro m hm
  have hcons : Submission.initTable n = 1 :: List.replicate n 0 := rfl
  by_cases hz : m = 0
  · -- column 0 is the head of the table, and it is 1
    rw [hz, if_pos rfl, hcons]
    rfl
  · -- every other column is a zero, and `partAux 0 m = 0` there
    have hpos : 0 < m := Nat.pos_of_ne_zero hz
    rw [hcons, nthNat_getD, if_neg hz]
    show (1 :: List.replicate n 0).getD m 0 = partAux 0 m
    -- `m > 0`, so `getD` steps past the head into the zeros
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_lt hpos)
    -- the table is `1` followed by `n` zeros, so any column past 0 reads a zero
    -- the head was already stepped over, so the read lands in the replicate of
    -- zeros, which is 0
    -- normalise the index in both the goal and the hypotheses, then destructure
    -- it as a successor (`hpos` guarantees the successor shape)
    simp only [Nat.zero_add] at hz hpos ⊢
    obtain ⟨j, hk⟩ := Nat.exists_eq_succ_of_ne_zero hz
    rw [hk]
    show (1 :: List.replicate n 0).getD (j + 1) 0 = partAux 0 (j + 1)
    -- the RHS is `partAux 0 (j+1)`, which is the same column as `partAux 0 j`
    -- because `partAux k m` does not depend on m
    rw [List.getD_cons_succ]
    have hz1 := nthNat_replicate_zero n j
    rw [nthNat_getD] at hz1
    rwa [List.getD_eq_getElem?_getD] at hz1

/-- One row step advances the invariant. The row step is the spec's sum over
multiplicities, and each summand is the predecessor column, which the
hypothesis already identifies with `partAux k`. The `m = 0` term is the one
place the "always 1" convention matters, and `partAux_zero` reconciles it.

The length is preserved by `length_updRowAdd`, and `updRowAdd` needs `0 < d`,
which is why this is stated at `k + 1`. -/
theorem inv_step (k : Nat) (len : Nat) (f : Nat → Nat) (h : Inv k len f) :
    Inv (k + 1) len (T (k + 1) f) := by
  intro m hm
  -- every column the step reads is at most m, hence in range
  have hsub : ∀ j, j * (k + 1) ≤ m → m - j * (k + 1) < len := by
    intro j hj
    have h2 : m - j * (k + 1) ≤ m := Nat.sub_le _ _
    have h3 : m < len := hm
    omega
  unfold T
  by_cases hz : m = 0
  · rw [if_pos hz]
    -- column 0 stays 1: the only summand is f 0
    show msum (fun j => f (m - j * (k + 1))) (m / (k + 1) + 1) = 1
    -- the range is m / (k+1) + 1, and with m = 0 that is 0 + 1, so `msum_succ`
    -- peels off the single summand, which reads column 0
    subst hz
    have hq : 0 / (k + 1) = 0 := by simp
    have hq' : 0 - 0 * (k + 1) = 0 := by simp
    rw [hq, Nat.zero_add, msum_succ, msum_zero, Nat.add_zero, hq']
    have h0 := h 0 (by omega)
    rw [if_pos rfl] at h0
    omega
  · rw [if_neg hz]
    show msum (fun j => f (m - j * (k + 1))) (m / (k + 1) + 1) = partAux (k + 1) m
    rw [partAux_eq_msum]
    refine msum_congr _ ?_
    intro j hj
    -- `j < m / (k+1) + 1` is exactly `j * (k+1) ≤ m`
    have hjle : j * (k + 1) ≤ m := by
      have hlt : j < m / (k + 1) + 1 := hj
      have h2 : j ≤ m / (k + 1) := by omega
      exact Nat.mul_le_of_le_div (k + 1) j m h2
    have hsub' := hsub j hjle
    have hc := h (m - j * (k + 1)) hsub'
    by_cases hzero : m - j * (k + 1) = 0
    · -- the predecessor column is the "empty partition" column, and both
      -- the invariant and `partAux_zero` call it 1
      have hc0 := h (m - j * (k + 1)) hsub'
      rw [hzero, if_pos rfl] at hc0
      rw [hzero, hc0]
      exact (partAux_zero k).symm
    · rw [if_neg hzero] at hc
      exact hc

/-- `succRange (k+1)` is `k+1` in front of `succRange k`, and the same list
written in the other order. Only the front-cons form is ever used. -/
theorem succRange_cons (k : Nat) :
    (k + 1) :: succRange k = succRange (k + 1) := succRange_succ k

/-- `succRange (k+1)` is the size-`k+1` step in front of the smaller ones.
This is definitional, and it is the form `coin` peels with `coin_cons`. -/
theorem coin_succRange (k : Nat) (f : Nat → Nat) :
    ∀ m, coin (succRange (k + 1)) f m = T (k + 1) (coin (succRange k) f) m := by
  intro m
  rw [succRange_succ, coin_cons]

/-- Every size in `succRange k` is positive: the list holds `k, k-1, …, 1`,
all successors. -/
theorem succRange_pos (k : Nat) : ∀ y ∈ succRange k, 0 < y := by
  induction k with
  | zero =>
    intro y hy
    cases hy
  | succ k ih =>
    intro y hy
    rw [succRange_succ, List.mem_cons] at hy
    rcases hy with h | hy
    · have hpos : 0 < k + 1 := Nat.succ_pos k
      rw [h]
      exact hpos
    · exact ih y hy

/-- A step of size `x` applied *after* the steps in `ds` is the same operator
as that step applied *before* them — the two differ only in where the step sits
in the list. This is the pointwise form of the commutation in `Coin.lean`, and
it is what lets a step be moved to the front of the list. -/
theorem coin_step (ds : List Nat) (x : Nat) (f : Nat → Nat) :
    ∀ m, coin ds (T x f) m = coin (ds ++ [x]) f m := by
  induction ds with
  | nil =>
    intro m
    rfl
  | cons d ds ih =>
    intro m
    rw [coin_cons, List.cons_append]
    -- both sides are `T d` applied at column `m`, and the IH says the two
    -- arguments agree at *every* column, so they agree as functions
    have h := ih
    have hfun : coin ds (T x f) = coin (ds ++ [x]) f := by
      funext c
      exact h c
    rw [hfun, coin_cons]

/-- `coin ds f` only ever reads `f` at columns *at or below* its own argument:
the head sums `f (c - j*d)` over `j`, and each such index is `≤ c`; the tail is
read at `c` itself. So agreement on columns `< n` propagates through `coin` on
columns `< n`.

This is the reason the whole proof can be stated on column-reading functions
instead of on lists: nothing downstream ever looks at a column above the one
it was asked about, so the list's length only has to cover the queried column. -/
theorem coin_congr (ds : List Nat) {f g : Nat → Nat} {n : Nat}
    (h : ∀ c, c < n → f c = g c) :
    ∀ c, c < n → coin ds f c = coin ds g c := by
  induction ds with
  | nil =>
    intro c hc
    exact h c hc
  | cons d ds ih =>
    intro c hc
    rw [coin_cons]
    unfold T
    refine msum_congr _ ?_
    intro j _
    have hle : c - j * d ≤ c := Nat.sub_le _ _
    have hlt : c - j * d < n := by omega
    exact ih (c - j * d) hlt

/-- `itAdd k t` applies the row steps of sizes `k, k-1, …, 1`, and `coin`
applied to that list computes the same column-reading function.

The statement is pointwise and bounded by `m < t.length`. That is not a
restriction: `nthNat` reads 0 past the end, but `T` does not, so the two
functions genuinely differ outside the range and only agree inside it. -/
theorem itAdd_coin (k : Nat) (t : List Nat) (m : Nat) (hm : m < t.length) :
    Submission.nthNat (Submission.itAdd k t) m
      = coin (succRange k) (Submission.nthNat t) m := by
  induction k generalizing t with
  | zero =>
    rfl
  | succ k ih =>
    -- `itAdd (k+1) t = itAdd k (updRowAdd (k+1) t)`, and the step preserves the
    -- length, so the queried column stays in range for the k remaining steps
    have hlen : m < (Submission.updRowAdd (k + 1) t).length := by
      rw [length_updRowAdd (k + 1) t (Nat.succ_pos k)]
      exact hm
    rw [Submission.itAdd, ih _ hlen]
    -- substitute the stepped table's column function with `T (k+1)` of the
    -- original; `coin_congr` propagates the pointwise equality through `coin`,
    -- which only ever reads columns at or below the one it is asked for
    have hcol : ∀ c, c < t.length →
        Submission.nthNat (Submission.updRowAdd (k + 1) t) c
          = T (k + 1) (Submission.nthNat t) c := by
      intro c hc
      have hmsum := nthNat_updRowAdd_eq_msum (k + 1) (Nat.succ_pos k) t c hc
      show Submission.nthNat (Submission.updRowAdd (k + 1) t) c
        = T (k + 1) (Submission.nthNat t) c
      unfold T
      exact hmsum
    rw [succRange_succ, coin_cons]
    rw [coin_congr (succRange k) hcol m hm]
    -- move the size-(k+1) step to the front of the list: the operator is
    -- unchanged, and `coin_append` then peels it off. This is the commutation
    -- result from `Coin.lean`, and it is the one place where the
    -- implementation's decreasing iteration order is reconciled with the
    -- spec's increasing recurrence.
    rw [coin_step]
    exact (coin_append (succRange k) (succRange_pos k) (k + 1) (Nat.succ_pos k)
      (Submission.nthNat t)) m

/-- A row step of size `d` on the table is, on the column-reading function,
exactly the operator `T d`. This is the pointwise form of
`nthNat_updRowAdd_eq_msum`, and it is what lets the invariant be stated on
functions instead of on lists. -/
theorem nthNat_updRowAdd_T (d : Nat) (hd : 0 < d) (t : List Nat) (m : Nat)
    (hm : m < t.length) :
    Submission.nthNat (Submission.updRowAdd d t) m
      = T d (Submission.nthNat t) m :=
  nthNat_updRowAdd_eq_msum d hd t m hm
/-- Iterating the invariant over the whole size list: if the table satisfies
`Inv k` then applying the row step of size `k+1` gives `Inv (k+1)`. The list
`succRange (k+1)` puts that step in front, so `coin_congr` and `coin_cons`
chain the steps in increasing order — the order `inv_step` needs. -/
theorem inv_coin (n : Nat) (len : Nat) (f : Nat → Nat) (h : Inv 0 len f) :
    Inv n len (coin (succRange n) f) := by
  induction n with
  | zero =>
    -- no steps: the table is unchanged, and the base invariant is exactly Inv 0
    intro m hm
    exact h m hm
  | succ n ih =>
    -- `coin (succRange (n+1)) f = T (n+1) (coin (succRange n)) f`; apply the
    -- inductive hypothesis to get `Inv n` on the inner composition, then one
    -- `inv_step` to advance it to `Inv (n+1)`.
    -- `len` and `f` are fixed, so the induction on `n` leaves both untouched
    have hinner : Inv n len (coin (succRange n) f) := ih
    have hcol : (fun m => coin (succRange (n + 1)) f m)
        = T (n + 1) (coin (succRange n) f) := by
      funext m
      exact coin_succRange n f m
    have hfinal := inv_step n len (coin (succRange n) f) hinner
    -- rewrite the column function from `T (n+1) ∘ coin` to `coin (succRange (n+1))`
    intro m hm
    have := hfinal m hm
    rwa [← hcol] at this
/-- The implementation computes `p(n)` for every `n`.

Three facts are chained:
  * `inv_init` puts the initial table in the `Inv 0` regime;
  * `inv_coin` carries that through all `n` row steps to `Inv n`, so column
    `m` reads `partAux n m` — the spec's value;
  * `itAdd_coin` identifies the actual streaming loop with `coin (succRange n)`.

The column read is `n`, and `initTable n` has length `n + 1`, so `n` is in
range. The result is `partAux n n`, which is `partitionSpec n`. -/
theorem impl_correct (n : Nat) :
    Submission.impl n = partitionSpec n := by
  unfold Submission.impl partitionSpec
  -- the initial table is in the `Inv 0` regime
  have h0 := inv_init n
  -- after all n row steps, the column function reads `partAux n`
  have hn := inv_coin n (Submission.initTable n).length
    (Submission.nthNat (Submission.initTable n)) h0
  -- the streaming loop computes that same column function
  have hit := itAdd_coin n (Submission.initTable n) n (by
    simp [Submission.initTable])
  -- column `n` is in range (the table has length `n + 1`) and is not `0`
  have hlen : n < (Submission.initTable n).length := by
    simp [Submission.initTable]
  have hcol := hn n hlen
  rw [hit, hcol]
  -- column `n` is never column `0` (except at n = 0, where `partAux 0 0 = 1`
  -- anyway), so the `if` collapses to `partAux n n`
  split
  · rename_i h
    subst h
    exact partAux_zero 0 |>.symm
  · rfl


end Probe


namespace Submission

/-- The implementation computes `p(n)`.

Chains `inv_init` (the 1-headed table is in the `Inv 0` regime), `inv_coin`
(all `n` row steps give `Inv n`, so column `m` reads `partAux n m`), and
`itAdd_coin` (the real streaming loop is `coin (succRange n)`). Reading column
`n` of the finished table therefore gives `partAux n n = partitionSpec n`. -/
theorem impl_correct : ∀ n, impl n = partitionSpec n := by
  intro n
  exact Probe.impl_correct n

end Submission
