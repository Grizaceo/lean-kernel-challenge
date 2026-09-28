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


/-! ### Unrolled initial word — v3

The v2 header measured steps 2/4/8 at 358.5M/359.5M/361.4M instructions and
read the ~357M gap to the leaderboard as a *list* cost. It is not. Measured
with the local instruction counter (scripts/icount.c), an isolated `caMix32`
call costs nothing, so 254 of them cannot be the cost either: the recursive
`initBitsAux` costs 2,769M and the *same value* unrolled costs 265M. The cost
was Lean's structural Nat recursion — `brecOn`/`Nat.rec` instantiated and
type-checked by the kernel on every one of 254 iterations. Cheaper arithmetic
does nothing: an incremental mix argument gives 0.8%, 32-bit byte lanes 0.5%.

So v3 emits the spec's own `encodeRow` foldr with the recursion removed. Cell
`i` sits at bit `i`; cells 0 and 1 are the spec's fixed head, never mixed. The
base is `2 * 0 + b255` because `foldr g 0` bottoms out there, not at `b255` —
matching it literally is what makes the proof syntactic rather than merely
extensional.
-/

-- 256 levels of nesting by construction.
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def initBits (seed : Nat) : Nat :=
  2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2
  * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 *
  (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2
  * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 *
  (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2
  * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 *
  (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2
  * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 *
  (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2
  * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 *
  (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2
  * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 *
  (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2
  * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 *
  (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2
  * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 *
  (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2
  * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * 0 + (if (caMix32 (seed +
  256 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  255 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  254 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  253 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  252 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  251 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  250 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  249 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  248 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  247 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  246 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  245 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  244 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  243 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  242 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  241 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  240 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  239 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  238 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  237 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  236 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  235 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  234 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  233 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  232 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  231 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  230 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  229 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  228 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  227 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  226 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  225 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  224 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  223 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  222 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  221 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  220 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  219 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  218 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  217 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  216 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  215 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  214 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  213 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  212 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  211 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  210 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  209 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  208 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  207 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  206 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  205 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  204 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  203 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  202 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  201 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  200 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  199 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  198 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  197 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  196 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  195 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  194 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  193 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  192 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  191 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  190 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  189 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  188 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  187 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  186 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  185 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  184 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  183 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  182 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  181 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  180 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  179 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  178 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  177 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  176 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  175 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  174 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  173 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  172 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  171 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  170 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  169 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  168 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  167 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  166 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  165 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  164 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  163 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  162 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  161 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  160 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  159 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  158 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  157 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  156 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  155 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  154 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  153 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  152 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  151 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  150 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  149 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  148 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  147 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  146 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  145 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  144 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  143 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  142 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  141 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  140 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  139 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  138 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  137 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  136 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  135 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  134 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  133 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  132 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  131 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  130 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  129 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  128 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  127 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  126 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  125 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  124 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  123 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  122 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  121 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  120 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  119 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  118 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  117 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  116 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  115 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  114 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  113 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  112 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  111 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  110 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  109 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  108 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  107 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  106 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  105 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  104 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  103 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  102 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  101 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed +
  100 * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed + 99
  * 0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed + 98 *
  0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed + 97 *
  0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed + 96 *
  0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed + 95 *
  0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed + 94 *
  0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed + 93 *
  0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed + 92 *
  0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed + 91 *
  0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed + 90 *
  0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed + 89 *
  0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed + 88 *
  0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed + 87 *
  0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed + 86 *
  0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed + 85 *
  0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed + 84 *
  0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed + 83 *
  0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed + 82 *
  0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed + 81 *
  0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed + 80 *
  0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed + 79 *
  0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed + 78 *
  0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed + 77 *
  0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed + 76 *
  0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed + 75 *
  0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed + 74 *
  0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed + 73 *
  0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed + 72 *
  0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed + 71 *
  0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed + 70 *
  0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed + 69 *
  0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed + 68 *
  0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed + 67 *
  0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed + 66 *
  0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed + 65 *
  0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed + 64 *
  0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed + 63 *
  0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed + 62 *
  0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed + 61 *
  0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed + 60 *
  0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed + 59 *
  0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed + 58 *
  0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed + 57 *
  0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed + 56 *
  0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed + 55 *
  0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed + 54 *
  0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed + 53 *
  0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed + 52 *
  0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed + 51 *
  0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed + 50 *
  0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed + 49 *
  0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed + 48 *
  0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed + 47 *
  0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed + 46 *
  0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed + 45 *
  0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed + 44 *
  0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed + 43 *
  0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed + 42 *
  0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed + 41 *
  0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed + 40 *
  0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed + 39 *
  0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed + 38 *
  0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed + 37 *
  0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed + 36 *
  0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed + 35 *
  0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed + 34 *
  0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed + 33 *
  0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed + 32 *
  0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed + 31 *
  0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed + 30 *
  0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed + 29 *
  0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed + 28 *
  0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed + 27 *
  0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed + 26 *
  0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed + 25 *
  0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed + 24 *
  0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed + 23 *
  0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed + 22 *
  0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed + 21 *
  0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed + 20 *
  0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed + 19 *
  0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed + 18 *
  0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed + 17 *
  0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed + 16 *
  0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed + 15 *
  0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed + 14 *
  0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed + 13 *
  0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed + 12 *
  0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed + 11 *
  0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed + 10 *
  0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed + 9 *
  0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed + 8 *
  0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed + 7 *
  0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed + 6 *
  0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed + 5 *
  0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed + 4 *
  0x09e3779b9)).testBit 31 then 1 else 0)) + (if (caMix32 (seed + 3 *
  0x09e3779b9)).testBit 31 then 1 else 0)) + 0) + 1

/-! ### Correctness of the unrolled initialization

Four lines, replacing v2's ~85-line simultaneous `testBit` induction. The spec
builds the row with `(List.range 256).map`, which `rfl` unfolds to a literal
list; `encodeRow` then reduces over that literal to exactly the nested term
above. -/

theorem rowLit (seed : Nat) : initRowFor seed = [
  true,
  false,
  (caMix32 (seed + 3 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 4 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 5 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 6 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 7 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 8 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 9 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 10 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 11 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 12 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 13 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 14 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 15 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 16 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 17 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 18 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 19 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 20 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 21 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 22 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 23 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 24 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 25 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 26 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 27 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 28 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 29 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 30 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 31 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 32 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 33 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 34 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 35 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 36 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 37 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 38 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 39 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 40 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 41 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 42 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 43 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 44 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 45 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 46 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 47 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 48 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 49 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 50 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 51 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 52 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 53 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 54 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 55 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 56 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 57 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 58 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 59 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 60 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 61 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 62 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 63 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 64 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 65 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 66 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 67 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 68 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 69 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 70 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 71 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 72 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 73 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 74 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 75 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 76 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 77 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 78 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 79 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 80 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 81 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 82 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 83 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 84 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 85 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 86 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 87 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 88 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 89 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 90 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 91 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 92 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 93 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 94 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 95 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 96 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 97 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 98 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 99 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 100 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 101 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 102 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 103 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 104 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 105 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 106 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 107 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 108 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 109 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 110 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 111 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 112 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 113 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 114 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 115 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 116 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 117 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 118 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 119 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 120 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 121 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 122 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 123 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 124 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 125 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 126 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 127 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 128 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 129 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 130 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 131 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 132 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 133 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 134 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 135 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 136 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 137 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 138 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 139 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 140 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 141 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 142 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 143 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 144 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 145 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 146 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 147 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 148 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 149 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 150 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 151 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 152 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 153 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 154 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 155 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 156 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 157 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 158 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 159 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 160 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 161 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 162 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 163 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 164 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 165 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 166 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 167 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 168 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 169 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 170 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 171 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 172 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 173 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 174 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 175 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 176 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 177 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 178 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 179 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 180 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 181 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 182 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 183 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 184 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 185 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 186 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 187 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 188 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 189 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 190 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 191 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 192 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 193 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 194 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 195 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 196 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 197 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 198 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 199 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 200 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 201 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 202 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 203 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 204 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 205 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 206 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 207 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 208 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 209 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 210 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 211 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 212 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 213 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 214 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 215 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 216 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 217 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 218 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 219 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 220 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 221 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 222 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 223 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 224 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 225 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 226 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 227 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 228 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 229 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 230 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 231 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 232 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 233 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 234 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 235 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 236 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 237 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 238 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 239 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 240 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 241 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 242 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 243 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 244 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 245 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 246 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 247 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 248 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 249 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 250 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 251 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 252 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 253 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 254 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 255 * 0x09e3779b9)).testBit 31,
  (caMix32 (seed + 256 * 0x09e3779b9)).testBit 31
] := by rfl

theorem initBits_eq (seed : Nat) :
    initBits seed = encodeRow (initRowFor seed) := by
  rw [rowLit seed]
  simp only [encodeRow, List.foldr_cons, List.foldr_nil, reduceIte]
  rfl

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
