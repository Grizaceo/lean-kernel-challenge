import Spec

/-! # Probe: where does the pentagonal correctness proof get stuck?

Target: prove the `impl` of candidates/partition-euler/Submission.lean against
`partitionSpec`. Copied here verbatim (modulo namespace) so the probe is
self-contained and does not touch the candidate. -/

namespace ProbeEuler

def nthInt : List Int → Nat → Int
  | [], _ => 0
  | x :: _, 0 => x
  | _ :: xs, i + 1 => nthInt xs i

structure Walk where
  g1 : Nat
  g2 : Nat
  step1 : Nat
  step2 : Nat
  pos : Bool

def psum : List Int → Nat → Walk → Nat → Int
  | _, _, _, 0 => 0
  | tbl, m, st, fuel + 1 =>
    if st.g1 > m then 0
    else
      let s := nthInt tbl (m - st.g1)
        + (if st.g2 ≤ m then nthInt tbl (m - st.g2) else 0)
      let here := if st.pos then s else -s
      here + psum tbl m
        { g1 := st.g1 + st.step1, g2 := st.g2 + st.step2
          step1 := st.step1 + 3, step2 := st.step2 + 3, pos := !st.pos }
        fuel

def build : List Int → Nat → Nat → List Int
  | tbl, _, 0 => tbl
  | tbl, m, fuel + 1 =>
    build (tbl ++ [psum tbl m ⟨1, 2, 4, 5, true⟩ (m + 1)]) (m + 1) fuel

def impl (n : Nat) : Nat :=
  (nthInt (build [1] 1 (n + 1)) n).toNat

/-! ## Attempt 1: direct strong induction on n.

The recurrence `psum` reads indices `m - g1(k)`, `m - g2(k)`. To close
`impl n = partitionSpec n` by induction we need

    psum tbl m st fuel = partitionSpec m

where `tbl` holds `partitionSpec` values at `0..m-1`. Unfolding one `psum`
step gives subgoals mentioning `partitionSpec (m - g1(k))` for *all* `k` up to
√(2m/3). Strong induction supplies exactly that. Try it.

The additional precondition on the *state*: after `k` steps the walk must be
at g1 = g1(k+1), g2 = g2(k+1), strides 3k+4 / 3k+5, sign (k+1) parity. Without
an invariant tying `st` to a `k`, the induction hypothesis cannot even name
the pentagonal offsets. State the invariant explicitly: -/

/-- Generalised pentagonal numbers by walk position. -/
def Walk.g1spec (k : Nat) : Nat := k * (3 * k - 1) / 2
def Walk.g2spec (k : Nat) : Nat := k * (3 * k + 1) / 2

theorem psum_matches_spec (m k : Nat) (hk : 0 < k) :
    ∀ (fuel : Nat),
      psum (List.range m |>.map fun i => (partitionSpec i : Int)) m
        ⟨Walk.g1spec k, Walk.g2spec k, 3 * k + 1, 3 * k + 2, k % 2 = 1⟩ fuel
        = (partitionSpec m : Int) := by
  induction m using Nat.strongRecOn with
  | _ m ih =>
    intro fuel
    cases fuel with
    | zero => sorry
    | succ fuel =>
      unfold psum
      split
      · sorry
      · -- The open goal here is essentially:
        --   (if h1 : Walk.g1spec k ≤ m then T (m - g1) else 0) with sign
        --     + (recursive psum at k+1) = partitionSpec m
        -- i.e. the FULL pentagonal identity
        --   p(m) = Σ_{k≥1} (-1)^{k+1} (p(m - g1 k) + p(m - g2 k))
        -- stated against the *spec* recurrence.  The `ih` only knows
        -- `partitionSpec` at smaller arguments through the same `psum`
        -- statement, so closing this goal requires a theorem of the form
        --
        --   partAux m m = Σ_{k≥1} (-1)^{k+1} (partAux .. (m-g1 k) + ...)   (*)
        --
        -- which does NOT follow by unfolding `partAux` (its recursion is by
        -- part size, not by pentagonal offsets).  Try the central rewrite:
        have key : ∀ n, (partitionSpec n : Int) =
            (if n = 0 then 1 else 0) := by
          intro n
          unfold partitionSpec partAux
          sorry
        sorry

end ProbeEuler
