import Spec

namespace Submission

/-! ## Optimized bit-parallel Rule 110 — v2

Playground measurement (2026-09-25): with the official bit-parallel `bstep`
kernel, slots with steps 2/4/8 cost 358.5M / 359.5M / 361.4M instructions —
per step ≈ 0.48M, so the *fixed* row initialization is ~357M (99.3%).
That initialization is `(List.range 256).map …` over `List Bool` with
`getD`/`%` per cell, then a `foldr`.

v2 keeps the exact proven `bstep` kernel and builds the initial 256-bit word
with a tail-recursive accumulator — no lists. Each cell: one `caMix32`,
one `testBit`, one shift, one OR. -/

/-! ### Trusted spec facts (as in the official example) -/

theorem testBit_encodeRow (row : List Bool) (i : Nat) :
    (encodeRow row).testBit i = row.getD i false := by
  induction row generalizing i with
  | nil => simp [encodeRow]
  | cons b bs ih =>
    have hrec : encodeRow (b :: bs) = 2 * encodeRow bs + (if b then 1 else 0) := rfl
    cases i with
    | zero => rw [hrec]; cases b <;> simp [Nat.testBit_zero] <;> omega
    | succ j =>
      rw [hrec, Nat.testBit_succ]
      have : (2 * encodeRow bs + (if b then 1 else 0)) / 2 = encodeRow bs := by
        cases b <;> simp <;> omega
      rw [this, ih]; rfl

theorem encodeRow_lt (row : List Bool) : encodeRow row < 2 ^ row.length := by
  induction row with
  | nil => simp [encodeRow]
  | cons b bs ih =>
    have hrec : encodeRow (b :: bs) = 2 * encodeRow bs + (if b then 1 else 0) := rfl
    rw [hrec, List.length_cons, Nat.pow_succ]; split <;> omega

@[simp] theorem length_stepRow (row : List Bool) : (stepRow row).length = row.length := by
  simp [stepRow]

theorem getD_stepRow (row : List Bool) (i : Nat) :
    (stepRow row).getD i false =
      if i < row.length then
        rule110 (row.getD ((i + row.length - 1) % row.length) false)
                (row.getD i false) (row.getD ((i + 1) % row.length) false)
      else false := by
  by_cases h : i < row.length
  · rw [List.getD_eq_getElem?_getD]; simp [stepRow, h]
  · have hlen : (stepRow row).length ≤ i := by rw [length_stepRow]; omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hlen, Option.getD_none, if_neg h]

/-! ### Bit-parallel kernel — identical to the official example -/

def M : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
theorem M_eq : M = 2 ^ 256 - 1 := by decide
theorem testBit_M (i : Nat) : M.testBit i = decide (i < 256) := by
  rw [M_eq, Nat.testBit_two_pow_sub_one]
theorem testBit_high {m : Nat} (hm : m < 2 ^ 256) {j : Nat} (hj : 256 ≤ j) : m.testBit j = false := by
  have hlt : m < 2 ^ j := Nat.lt_of_lt_of_le hm (Nat.pow_le_pow_right (by omega) hj)
  simp [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hlt]

theorem testBit_rotL {m : Nat} (hm : m < 2 ^ 256) {i : Nat} (hi : i < 256) :
    (((m <<< 1) ||| (m >>> 255)) &&& M).testBit i = m.testBit ((i + 255) % 256) := by
  rw [Nat.testBit_and, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftRight, testBit_M]
  simp only [hi, decide_true, Bool.and_true]
  rcases Nat.eq_zero_or_pos i with hi0 | hipos
  · subst hi0; simp
  · have h1 : (1 ≤ i) := hipos
    have hmod : (i + 255) % 256 = i - 1 := by omega
    have hhi : m.testBit (255 + i) = false := testBit_high hm (by omega)
    simp [h1, hmod, hhi]

theorem testBit_rotR {m : Nat} (hm : m < 2 ^ 256) {i : Nat} (hi : i < 256) :
    (((m >>> 1) ||| ((m &&& 1) <<< 255)) &&& M).testBit i = m.testBit ((i + 1) % 256) := by
  rw [Nat.testBit_and, Nat.testBit_or, Nat.testBit_shiftRight, Nat.testBit_shiftLeft, testBit_M]
  simp only [hi, decide_true, Bool.and_true]
  by_cases h255 : i = 255
  · subst h255
    have hmod : (255 + 1) % 256 = 0 := by decide
    have hhi : m.testBit (1 + 255) = false := testBit_high hm (by omega)
    rw [hmod]; simp [hhi]
  · have hmod : (i + 1) % 256 = i + 1 := by omega
    have hnot : ¬ (255 ≤ i) := by omega
    simp [hmod, hnot, Nat.add_comm 1 i]

def bstep (m : Nat) : Nat :=
  (M ^^^ (((M ^^^ m) &&& (M ^^^ (((m >>> 1) ||| ((m &&& 1) <<< 255)) &&& M))) |||
          ((((m <<< 1) ||| (m >>> 255)) &&& M) &&& m &&& (((m >>> 1) ||| ((m &&& 1) <<< 255)) &&& M)))) &&& M

def biter : Nat → Nat → Nat
  | 0, m => m
  | t + 1, m => biter t (bstep m)

/-! ### List-free initial word -/

/-- Cell content, exactly as in `Spec.initRowFor` (cells 0/1 are fixed). -/
def cellBit (seed i : Nat) : Bool :=
  if i = 0 then true
  else if i = 1 then false
  else (caMix32 (seed + (i + 1) * 0x9e3779b9)).testBit 31

/-- Packing invariant: `initBitsAux seed i acc` = cells `0…i-1` packed at
their natural positions OR'd with `acc <<< i`. Starts at `i = ruleWidth`
with `acc = 0`; each step prepends cell `i-1` at position `i-1`. -/
def initBitsAux (seed i : Nat) (acc : Nat) : Nat :=
  if i = 0 then acc
  else initBitsAux seed (i - 1) ((acc <<< 1) ||| (if cellBit seed (i - 1) then 1 else 0))

def initBits (seed : Nat) : Nat :=
  initBitsAux seed ruleWidth 0

/-! ### Correctness of the list-free initialization -/

/-- The spec's `initRowFor` is `List.range ruleWidth |>.map f`, so element `j`
is `f j` whenever `j < ruleWidth`, and `getD` past the end is `false`.

`List.getD_map` does not exist in this toolchain (verified against
`env.constants`, not assumed); the route is `getD → getElem?`, then
`List.getElem?_map`, then `getElem?_range` / `getElem?_eq_none` for the two
sides of `j < ruleWidth`. -/
theorem getD_initRowFor (seed j : Nat) :
    (initRowFor seed).getD j false = if j < ruleWidth then cellBit seed j else false := by
  rw [initRowFor, List.getD_eq_getElem?_getD, List.getElem?_map]
  by_cases hj : j < ruleWidth
  · rw [List.getElem?_range hj, if_pos hj]; rfl
  · rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_gt hj), if_neg hj]; rfl

theorem testBit_one_ge {m : Nat} (hm : 1 ≤ m) : (1 : Nat).testBit m = false := by
  obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  rw [Nat.testBit_succ, Nat.div_eq_of_lt (by omega)]
  simp

theorem testBit_zero_all (m : Nat) : (0 : Nat).testBit m = false := by
  simp [Nat.testBit]

/-- The low and high `testBit` facts cannot be inducted separately: the case
`j = i-1` of the low lemma needs the `i' ≤ j'` case one step down, so both
live in a single conjunction over the same induction on `i`. -/
theorem initBitsAux_testBit (seed i acc j : Nat) :
    (j < i → (initBitsAux seed i acc).testBit j = cellBit seed j) ∧
    (i ≤ j → (initBitsAux seed i acc).testBit j = (acc <<< i).testBit j) := by
  induction i generalizing acc j with
  | zero =>
    refine ⟨fun hj => absurd hj (by omega), fun _ => ?_⟩
    rw [initBitsAux, if_pos rfl, Nat.shiftLeft_zero]
  | succ k ih =>
    have hne : (k + 1) ≠ 0 := by omega
    have hstep : initBitsAux seed (k + 1) acc
        = initBitsAux seed k ((acc <<< 1) ||| (if cellBit seed k then 1 else 0)) := by
      rw [initBitsAux, if_neg hne]
      congr 1
    have hkey : ((acc <<< 1) ||| (if cellBit seed k then 1 else 0)).testBit 0 = cellBit seed k := by
      rw [Nat.testBit_or, Nat.testBit_shiftLeft]
      cases cellBit seed k <;> simp
    constructor
    · intro hj
      rw [hstep]
      rcases Nat.lt_or_ge j k with hjk | hjk
      · exact (ih _ _).1 hjk
      · have hjk_eq : j = k := by omega
        subst hjk_eq
        rw [(ih _ _).2 (by omega), Nat.testBit_shiftLeft]
        simp only [decide_true, Nat.le_refl, Nat.sub_self, Bool.true_and]
        exact hkey
    · intro hj
      rw [hstep, (ih _ _).2 (by omega)]
      have hkj : k ≤ j := by omega
      have hjk1 : 1 ≤ j - k := by omega
      have hsub : j - (k + 1) = j - k - 1 := by omega
      simp only [Nat.testBit_shiftLeft, Nat.testBit_or, hkj, hjk1]
      cases hcb : cellBit seed k with
      | false =>
        simp only [Bool.false_eq_true, if_false, testBit_zero_all,
                   hj, hsub, decide_true, Bool.true_and, Bool.or_false]
      | true =>
        simp only [if_true]
        rw [testBit_one_ge hjk1]
        simp only [Bool.or_false, hj, hsub, decide_true, Bool.true_and]

theorem testBit_initBitsAux_low (seed i acc j : Nat) (hj : j < i) :
    (initBitsAux seed i acc).testBit j = cellBit seed j := (initBitsAux_testBit seed i acc j).1 hj

theorem testBit_initBitsAux_high (seed i acc j : Nat) (hj : i ≤ j) :
    (initBitsAux seed i acc).testBit j = (acc <<< i).testBit j := (initBitsAux_testBit seed i acc j).2 hj


theorem initBits_eq (seed : Nat) : initBits seed = encodeRow (initRowFor seed) := by
  simp only [initBits]
  apply Nat.eq_of_testBit_eq
  intro j
  have h2 := testBit_encodeRow (initRowFor seed) j
  by_cases hj : j < ruleWidth
  · rw [testBit_initBitsAux_low seed ruleWidth 0 j hj, h2, getD_initRowFor, if_pos hj]
  · have hzero : (initBitsAux seed ruleWidth 0).testBit j = false :=
      testBit_initBitsAux_high seed ruleWidth 0 j (Nat.le_of_not_gt hj) |>.trans (by simp)
    rw [hzero, h2, getD_initRowFor, if_neg hj]

/-! ### Bridge to the spec (identical to the official example) -/

theorem step_eq {row : List Bool} (hlen : row.length = 256) :
    encodeRow (stepRow row) = bstep (encodeRow row) := by
  have hm : encodeRow row < 2 ^ 256 := hlen ▸ encodeRow_lt row
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_encodeRow, getD_stepRow, hlen]
  by_cases hi : i < 256
  · rw [if_pos hi]
    have he : i + 256 - 1 = i + 255 := by omega
    rw [he]
    simp only [bstep, Nat.testBit_and, Nat.testBit_xor, Nat.testBit_or, testBit_M,
               testBit_rotL hm hi, testBit_rotR hm hi, testBit_encodeRow, hi, decide_true]
    generalize row.getD ((i + 255) % 256) false = a
    generalize row.getD i false = b
    generalize row.getD ((i + 1) % 256) false = c
    cases a <;> cases b <;> cases c <;> decide
  · rw [if_neg hi]
    unfold bstep
    rw [Nat.testBit_and, testBit_M, decide_eq_false hi, Bool.and_false]

theorem iter_eq : ∀ (n : Nat) (row : List Bool), row.length = 256 →
    encodeRow (iterRow n row) = biter n (encodeRow row) := by
  intro n
  induction n with
  | zero => intro row _; rfl
  | succ k ih =>
    intro row hlen
    show encodeRow (iterRow k (stepRow row)) = biter k (bstep (encodeRow row))
    rw [ih (stepRow row) (by rw [length_stepRow, hlen]), step_eq hlen]

def impl : Nat → Nat := fun n =>
  biter (caSteps n) (initBits (caSeed n))

theorem impl_correct : ∀ n, impl n = caSpecN n := by
  intro n
  show biter (caSteps n) (initBits (caSeed n)) =
    encodeRow (iterRow (caSteps n) (initRowFor (caSeed n)))
  rw [initBits_eq, iter_eq (caSteps n) (initRowFor (caSeed n))
    (by simp [initRowFor, ruleWidth])]

end Submission
