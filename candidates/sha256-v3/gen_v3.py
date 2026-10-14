#!/usr/bin/env python3
"""Generate candidates/sha256-v3/Submission.lean."""
from pathlib import Path

ROOT = Path("/home/gris96/.hermes/workspace/repos/SAIR/lean-kernel-challenge")
CAND_DIR = ROOT / "candidates" / "sha256-v3"
CAND_DIR.mkdir(parents=True, exist_ok=True)
DST = CAND_DIR / "Submission.lean"

K = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5,
    0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
    0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc,
    0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
    0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
    0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3,
    0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5,
    0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
    0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
]

IV = [
    0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
    0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
]

W32 = "(nat_lit 4294967295)"

def rotr_u(x: str, r: int) -> str:
    l = 32 - r
    return f"(Nat.lor (Nat.shiftRight {x} (nat_lit {r})) (Nat.shiftLeft {x} (nat_lit {l})))"

def small_sigma0_u(x: str) -> str:
    return f"(Nat.xor (Nat.xor {rotr_u(x, 7)} {rotr_u(x, 18)}) (Nat.shiftRight {x} (nat_lit 3)))"

def small_sigma1_u(x: str) -> str:
    return f"(Nat.xor (Nat.xor {rotr_u(x, 17)} {rotr_u(x, 19)}) (Nat.shiftRight {x} (nat_lit 10)))"

def big_sigma0_u(x: str) -> str:
    return f"(Nat.xor (Nat.xor {rotr_u(x, 2)} {rotr_u(x, 13)}) {rotr_u(x, 22)})"

def big_sigma1_u(x: str) -> str:
    return f"(Nat.xor (Nat.xor {rotr_u(x, 6)} {rotr_u(x, 11)}) {rotr_u(x, 25)})"

def ch_u(e: str, f: str, g: str) -> str:
    return f"(Nat.xor (Nat.land {e} {f}) (Nat.land (Nat.xor {e} {W32}) {g}))"

def maj_u(a: str, b: str, c: str) -> str:
    return f"(Nat.xor (Nat.land {a} (Nat.xor {b} {c})) (Nat.land {b} {c}))"

def add32_inline(a: str, b: str) -> str:
    return f"(Nat.land (Nat.add {a} {b}) {W32})"

def next_word_inline(w14: str, w9: str, w1: str, w0: str) -> str:
    return f"(Nat.land (Nat.add (Nat.add {small_sigma1_u(w14)} {w9}) (Nat.add {small_sigma0_u(w1)} {w0})) {W32})"

def t1_inline(e: str, f: str, g: str, h: str, k_expr: str, w: str) -> str:
    return f"(Nat.add {h} (Nat.add {big_sigma1_u(e)} (Nat.add {ch_u(e, f, g)} (Nat.add {k_expr} {w}))))"

def t2_inline(a: str, b: str, c: str) -> str:
    return f"(Nat.add {big_sigma0_u(a)} {maj_u(a, b, c)})"

g_lines = [
    "  let w_0 := w0.x0; let w_1 := w0.x1; let w_2 := w0.x2; let w_3 := w0.x3",
    "  let w_4 := w0.x4; let w_5 := w0.x5; let w_6 := w0.x6; let w_7 := w0.x7",
    "  let w_8 := w0.x8; let w_9 := w0.x9; let w_10 := w0.x10; let w_11 := w0.x11",
    "  let w_12 := w0.x12; let w_13 := w0.x13; let w_14 := w0.x14; let w_15 := w0.x15",
    "  let a_0 := s0.a; let b_0 := s0.b; let c_0 := s0.c; let d_0 := s0.d",
    "  let e_0 := s0.e; let f_0 := s0.f; let g_0 := s0.g; let h_0 := s0.h",
]

# Build g_lines (for stepUnrolledG) and hoisted r_lines (for fastStepR)
sa_g = ["a_0", "b_0", "c_0", "d_0"]
se_g = ["e_0", "f_0", "g_0", "h_0"]

for i in range(64):
    if i >= 16:
        g_lines.append(f"  let w_{i} := nxt w_{i-2} w_{i-7} w_{i-15} w_{i-16}")
    a, b, c, d_v = sa_g
    e, f_v, g, h = se_g
    k_lit = f"(nat_lit {K[i]})"
    g_lines.append(f"  let t1_{i} := t1F {e} {f_v} {g} {h} {k_lit} w_{i}")
    g_lines.append(f"  let t2_{i} := t2F {a} {b} {c}")
    g_lines.append(f"  let na_{i} := addF t1_{i} t2_{i}")
    g_lines.append(f"  let ne_{i} := addF {d_v} t1_{i}")
    sa_g = [f"na_{i}", a, b, c]
    se_g = [f"ne_{i}", e, f_v, g]

g_lines.append(
    f"  ⟨addF s0.a {sa_g[0]}, addF s0.b {sa_g[1]}, addF s0.c {sa_g[2]}, addF s0.d {sa_g[3]}, "
    f"addF s0.e {se_g[0]}, addF s0.f {se_g[1]}, addF s0.g {se_g[2]}, addF s0.h {se_g[3]}⟩"
)

r_lines = []
w_fields = ["d.a", "d.b", "d.c", "d.d", "d.e", "d.f", "d.g", "d.h"]
w_r = [
    "w_0", "w_1", "w_2", "w_3", "w_4", "w_5", "w_6", "w_7",
    "(nat_lit 0x80000000)", "(nat_lit 0)", "(nat_lit 0)", "(nat_lit 0)",
    "(nat_lit 0)", "(nat_lit 0)", "(nat_lit 0)", "(nat_lit 256)",
]
sa_r = [f"(nat_lit {IV[0]})", f"(nat_lit {IV[1]})", f"(nat_lit {IV[2]})", f"(nat_lit {IV[3]})"]
se_r = [f"(nat_lit {IV[4]})", f"(nat_lit {IV[5]})", f"(nat_lit {IV[6]})", f"(nat_lit {IV[7]})"]

for i in range(64):
    if i < 8:
        r_lines.append(f"  let w_{i} := {w_fields[i]}")
    elif i >= 16:
        nw = next_word_inline(w_r[i - 2], w_r[i - 7], w_r[i - 15], w_r[i - 16])
        if i <= 61:
            r_lines.append(f"  let w_{i} := {nw}")
            w_r.append(f"w_{i}")
        else:
            w_r.append(nw)
    ar, br, cr, dr = sa_r
    er, fr, gr, hr = se_r
    k_lit = f"(nat_lit {K[i]})"
    r_lines.append(f"  let t1_{i} := {t1_inline(er, fr, gr, hr, k_lit, w_r[i])}")
    na_expr = add32_inline(f"t1_{i}", t2_inline(ar, br, cr))
    ne_expr = add32_inline(dr, f"t1_{i}")
    if i < 63:
        r_lines.append(f"  let na_{i} := {na_expr}")
        r_lines.append(f"  let ne_{i} := {ne_expr}")
        sa_r = [f"na_{i}", ar, br, cr]
        se_r = [f"ne_{i}", er, fr, gr]
    else:
        sa_r = [na_expr, ar, br, cr]
        se_r = [ne_expr, er, fr, gr]

r_lines.append(
    f"  ⟨{add32_inline(f'(nat_lit {IV[0]})', sa_r[0])}, {add32_inline(f'(nat_lit {IV[1]})', sa_r[1])}, "
    f"{add32_inline(f'(nat_lit {IV[2]})', sa_r[2])}, {add32_inline(f'(nat_lit {IV[3]})', sa_r[3])}, "
    f"{add32_inline(f'(nat_lit {IV[4]})', se_r[0])}, {add32_inline(f'(nat_lit {IV[5]})', se_r[1])}, "
    f"{add32_inline(f'(nat_lit {IV[6]})', se_r[2])}, {add32_inline(f'(nat_lit {IV[7]})', se_r[3])}⟩"
)

round_defs_str = ""
r_body = "\n".join(r_lines)

g_body = "\n".join(g_lines)

src = f"""import Spec

/-!
# sha256-v3 — Mask-Eliminated Unrolled Primitive SHA-256 Compression Step

Compared to `sha256-v2`:
1. Eliminates all 7 `Nat.land ... 0xffffffff` masks inside `t1R` (`t1U` has 0 masks)
   and all 4 `Nat.land ... 0xffffffff` masks inside `t2R` (`t2U` has 0 masks),
   deferring modular reduction mod `2^32` to `na_i := add32R t1_i t2_i` and
   `ne_i := add32R d_i t1_i`.
2. Eliminates 6 of the 7 `Nat.land ... 0xffffffff` masks inside `nextWordR`
   (leaving only the single final mask on `s1 + w9 + s0 + w0`).
3. Factors `maj a b c` as `(a &&& (b ^^^ c)) ^^^ (b &&& c)` (4 ops instead of 5).
In total, removes 1,056 primitive operations per block (1,157,376 operations
across the 6 judge slots) while keeping a < 1s reflexive spine proof.
-/

namespace Submission

structure Window where
  x0 : Nat
  x1 : Nat
  x2 : Nat
  x3 : Nat
  x4 : Nat
  x5 : Nat
  x6 : Nat
  x7 : Nat
  x8 : Nat
  x9 : Nat
  x10 : Nat
  x11 : Nat
  x12 : Nat
  x13 : Nat
  x14 : Nat
  x15 : Nat

def Window.toList (w : Window) : List Nat :=
  [w.x0, w.x1, w.x2, w.x3, w.x4, w.x5, w.x6, w.x7,
   w.x8, w.x9, w.x10, w.x11, w.x12, w.x13, w.x14, w.x15]

def Window.nextWord (w : Window) : Nat :=
  add32 (add32 (smallSigma1 w.x14) w.x9)
    (add32 (smallSigma0 w.x1) w.x0)

def Window.push (w : Window) (x : Nat) : Window :=
  ⟨w.x1, w.x2, w.x3, w.x4, w.x5, w.x6, w.x7, w.x8,
   w.x9, w.x10, w.x11, w.x12, w.x13, w.x14, w.x15, x⟩

def generate : Nat → Window → List Nat
  | 0, _ => []
  | k + 1, w =>
      let x := w.nextWord
      x :: generate k (w.push x)

def initialWindow (d : Digest) : Window :=
  ⟨d.a, d.b, d.c, d.d, d.e, d.f, d.g, d.h,
   0x80000000, 0, 0, 0, 0, 0, 0, 256⟩

def initialWindowR (d : Digest) : Window :=
  ⟨d.a, d.b, d.c, d.d, d.e, d.f, d.g, d.h,
   (nat_lit 0x80000000), (nat_lit 0), (nat_lit 0), (nat_lit 0),
   (nat_lit 0), (nat_lit 0), (nat_lit 0), (nat_lit 256)⟩

def ivR : Digest :=
  ⟨(nat_lit 0x6a09e667), (nat_lit 0xbb67ae85), (nat_lit 0x3c6ef372), (nat_lit 0xa54ff53a),
   (nat_lit 0x510e527f), (nat_lit 0x9b05688c), (nat_lit 0x1f83d9ab), (nat_lit 0x5be0cd19)⟩

def fastSchedule (d : Digest) : List Nat :=
  let w := initialWindow d
  w.toList ++ generate 48 w

def fastStep (d : Digest) : Digest :=
  let f := rounds (K.zip (fastSchedule d)) iv
  ⟨add32 iv.a f.a, add32 iv.b f.b, add32 iv.c f.c, add32 iv.d f.d,
   add32 iv.e f.e, add32 iv.f f.f, add32 iv.g f.g, add32 iv.h f.h⟩

def w32R : Nat := (nat_lit 0xFFFFFFFF)
def add32R (a b : Nat) : Nat := (Nat.land (Nat.add a b) (nat_lit 4294967295))
def nextWordR (w14 w9 w1 w0 : Nat) : Nat := {next_word_inline("w14", "w9", "w1", "w0")}
def t1U (e f g h k w : Nat) : Nat := {t1_inline("e", "f", "g", "h", "k", "w")}
def t2U (a b c : Nat) : Nat := {t2_inline("a", "b", "c")}

def genG (nxt : Nat → Nat → Nat → Nat → Nat) : Nat → Window → List Nat
  | 0, _ => []
  | k + 1, w =>
      let x := nxt w.x14 w.x9 w.x1 w.x0
      x :: genG nxt k (w.push x)

def mkRoundG (t1F : Nat → Nat → Nat → Nat → Nat → Nat → Nat)
    (t2F : Nat → Nat → Nat → Nat) (addF : Nat → Nat → Nat)
    (s : Digest) (k w : Nat) : Digest :=
  let t1 := t1F s.e s.f s.g s.h k w
  let t2 := t2F s.a s.b s.c
  ⟨addF t1 t2, s.a, s.b, s.c, addF s.d t1, s.e, s.f, s.g⟩

def roundsG (rnd : Digest → Nat → Nat → Digest) : List (Nat × Nat) → Digest → Digest
  | [], s => s
  | (k, w) :: rest, s => roundsG rnd rest (rnd s k w)

def stepListG (t1F : Nat → Nat → Nat → Nat → Nat → Nat → Nat)
    (t2F : Nat → Nat → Nat → Nat) (addF : Nat → Nat → Nat)
    (nxt : Nat → Nat → Nat → Nat → Nat) (w0 : Window) (s0 : Digest) : Digest :=
  let f := roundsG (mkRoundG t1F t2F addF) (K.zip (w0.toList ++ genG nxt 48 w0)) s0
  ⟨addF s0.a f.a, addF s0.b f.b, addF s0.c f.c, addF s0.d f.d,
   addF s0.e f.e, addF s0.f f.f, addF s0.g f.g, addF s0.h f.h⟩

def stepUnrolledG (t1F : Nat → Nat → Nat → Nat → Nat → Nat → Nat)
    (t2F : Nat → Nat → Nat → Nat) (addF : Nat → Nat → Nat)
    (nxt : Nat → Nat → Nat → Nat → Nat) (w0 : Window) (s0 : Digest) : Digest :=
{g_body}

theorem stepUnrolledG_eq (t1F : Nat → Nat → Nat → Nat → Nat → Nat → Nat)
    (t2F : Nat → Nat → Nat → Nat) (addF : Nat → Nat → Nat)
    (nxt : Nat → Nat → Nat → Nat → Nat) (w0 : Window) (s0 : Digest) :
    stepUnrolledG t1F t2F addF nxt w0 s0 = stepListG t1F t2F addF nxt w0 s0 := rfl

{round_defs_str}

def fastStepR (d : Digest) : Digest :=
{r_body}

theorem fastStepR_eq_unrolled (d : Digest) :
    fastStepR d = stepUnrolledG t1U t2U add32R nextWordR (initialWindowR d) ivR := rfl

def seedStep32R (x : Nat) : Nat :=
  Nat.land (Nat.add (Nat.mul (nat_lit 1664525) x) (nat_lit 1013904223)) w32R

def seedDigestR (seed : Nat) : Digest :=
  let a := seedStep32R (Nat.land seed w32R)
  let b := seedStep32R a
  let c := seedStep32R b
  let d := seedStep32R c
  let e := seedStep32R d
  let f := seedStep32R e
  let g := seedStep32R f
  let h := seedStep32R g
  ⟨a, b, c, d, e, f, g, h⟩

def m32R : Nat := (nat_lit 4294967296)

def encodeDigestR (d : Digest) : Nat :=
  Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul d.a m32R) d.b) m32R) d.c) m32R) d.d) m32R) d.e) m32R) d.f) m32R) d.g) m32R) d.h

noncomputable def iterDigestR (step : Digest → Digest) (t : Nat) : Digest → Digest :=
  @Nat.rec (fun _ => Digest → Digest) (fun d => d) (fun _ ih d => ih (step d)) t

noncomputable def impl (n : Nat) : Nat :=
  encodeDigestR (iterDigestR fastStepR (Nat.shiftRight n (nat_lit 32)) (seedDigestR (Nat.land n w32R)))

/-! ### Correctness proof -/

theorem hand_eq (x y : Nat) : (x &&& y) = Nat.land x y := rfl
theorem hxor_eq (x y : Nat) : (x ^^^ y) = Nat.xor x y := rfl
theorem hor_eq (x y : Nat) : (x ||| y) = Nat.lor x y := rfl
theorem hshl_eq (x y : Nat) : (x <<< y) = Nat.shiftLeft x y := rfl
theorem hshr_eq (x y : Nat) : (x >>> y) = Nat.shiftRight x y := rfl
theorem hadd_eq (x y : Nat) : (x + y) = Nat.add x y := rfl
theorem hsub_eq (x y : Nat) : (x - y) = Nat.sub x y := rfl
theorem hmul_eq (x y : Nat) : (x * y) = Nat.mul x y := rfl
theorem w32R_eq : w32 = w32R := rfl
theorem m32R_eq : (4294967296 : Nat) = m32R := rfl

theorem and_w32_eq_mod (x : Nat) : (x &&& w32) = x % 2 ^ 32 := by
  change x &&& (2 ^ 32 - 1) = x % 2 ^ 32
  exact Nat.and_two_pow_sub_one_eq_mod x 32

theorem add32_eq_mod (a b : Nat) : add32 a b = (a + b) % 2 ^ 32 := by
  unfold add32; exact and_w32_eq_mod (a + b)

theorem add32_left_mask (a b : Nat) : add32 (a &&& w32) b = add32 a b := by
  rw [add32_eq_mod, add32_eq_mod, and_w32_eq_mod, Nat.mod_add_mod]

theorem add32_right_mask (a b : Nat) : add32 a (b &&& w32) = add32 a b := by
  rw [add32_eq_mod, add32_eq_mod, and_w32_eq_mod, Nat.add_mod_mod]

theorem add32R_eq (a b : Nat) : add32R a b = add32 a b := by
  unfold add32R add32; simp only [hand_eq, hadd_eq, w32R_eq]; rfl

theorem add32R_left_mask (a b : Nat) : add32R (Nat.land a w32R) b = add32R a b :=
  add32_left_mask a b

theorem add32R_right_mask (a b : Nat) : add32R a (Nat.land b w32R) = add32R a b :=
  add32_right_mask a b

theorem land_xor_distrib (a b c : Nat) :
    Nat.land (Nat.xor a b) c = Nat.xor (Nat.land a c) (Nat.land b c) :=
  Nat.and_xor_distrib_right

theorem land_w32R_idem (x : Nat) :
    Nat.land (Nat.land x w32R) w32R = Nat.land x w32R := by
  change (x &&& w32) &&& w32 = x &&& w32
  rw [Nat.and_assoc]; rfl

def rotr32U (x r l : Nat) : Nat :=
  Nat.lor (Nat.shiftRight x r) (Nat.shiftLeft x l)

theorem rotr32U_mask (x n : Nat) :
    Nat.land (rotr32U x n (Nat.sub (nat_lit 32) n)) w32R = rotr32 x n := by
  unfold rotr32U rotr32
  simp only [hand_eq, hor_eq, hshr_eq, hshl_eq, hsub_eq, w32R_eq]

def smallSigma0U (x : Nat) : Nat :=
  {small_sigma0_u("x")}

def smallSigma1U (x : Nat) : Nat :=
  {small_sigma1_u("x")}

def bigSigma0U (x : Nat) : Nat :=
  {big_sigma0_u("x")}

def bigSigma1U (x : Nat) : Nat :=
  {big_sigma1_u("x")}

theorem smallSigma0U_mask (x : Nat) : Nat.land (smallSigma0U x) w32R = Nat.land (smallSigma0 x) w32R := by
  unfold smallSigma0
  rw [← rotr32U_mask x 7, ← rotr32U_mask x 18]
  unfold smallSigma0U rotr32U
  simp only [hxor_eq, hshr_eq, land_xor_distrib, land_w32R_idem]

theorem smallSigma1U_mask (x : Nat) : Nat.land (smallSigma1U x) w32R = Nat.land (smallSigma1 x) w32R := by
  unfold smallSigma1
  rw [← rotr32U_mask x 17, ← rotr32U_mask x 19]
  unfold smallSigma1U rotr32U
  simp only [hxor_eq, hshr_eq, land_xor_distrib, land_w32R_idem]

theorem bigSigma0U_mask (x : Nat) : Nat.land (bigSigma0U x) w32R = Nat.land (bigSigma0 x) w32R := by
  unfold bigSigma0
  rw [← rotr32U_mask x 2, ← rotr32U_mask x 13, ← rotr32U_mask x 22]
  unfold bigSigma0U rotr32U
  simp only [hxor_eq, land_xor_distrib, land_w32R_idem]

theorem bigSigma1U_mask (x : Nat) : Nat.land (bigSigma1U x) w32R = Nat.land (bigSigma1 x) w32R := by
  unfold bigSigma1
  rw [← rotr32U_mask x 6, ← rotr32U_mask x 11, ← rotr32U_mask x 25]
  unfold bigSigma1U rotr32U
  simp only [hxor_eq, land_xor_distrib, land_w32R_idem]

theorem majU_eq (a b c : Nat) :
    {maj_u("a", "b", "c")} = maj a b c := by
  unfold maj
  rw [← Nat.and_xor_distrib_left]
  simp only [hxor_eq, hand_eq]

theorem w32_lit : w32 = (nat_lit 4294967295) := rfl

theorem chU_eq (e f g : Nat) :
    {ch_u("e", "f", "g")} = ch e f g := by
  unfold ch
  simp only [hxor_eq, hand_eq, w32_lit]

theorem nextWordR_eq (w14 w9 w1 w0 : Nat) :
    nextWordR w14 w9 w1 w0 = add32 (add32 (smallSigma1 w14) w9) (add32 (smallSigma0 w1) w0) := by
  have h1 : nextWordR w14 w9 w1 w0 = add32R (Nat.add (smallSigma1U w14) w9) (Nat.add (smallSigma0U w1) w0) := rfl
  rw [h1]
  have h2 : add32R (Nat.add (smallSigma1U w14) w9) (Nat.add (smallSigma0U w1) w0) =
      add32R (add32R (smallSigma1U w14) w9) (add32R (smallSigma0U w1) w0) := by
    rw [← add32R_left_mask (Nat.add (smallSigma1U w14) w9), ← add32R_right_mask _ (Nat.add (smallSigma0U w1) w0)]
    rfl
  rw [h2, ← add32R_left_mask (smallSigma1U w14) w9, smallSigma1U_mask, add32R_left_mask,
      ← add32R_left_mask (smallSigma0U w1) w0, smallSigma0U_mask, add32R_left_mask]
  simp only [add32R_eq]

def nextWordSpec (w14 w9 w1 w0 : Nat) : Nat :=
  add32 (add32 (smallSigma1 w14) w9) (add32 (smallSigma0 w1) w0)

theorem nextWordR_fun : nextWordR = nextWordSpec :=
  funext fun a => funext fun b => funext fun c => funext fun d => nextWordR_eq a b c d

def t1Spec (e f g h k w : Nat) : Nat :=
  add32 h (add32 (bigSigma1 e) (add32 (ch e f g) (add32 k w)))

theorem t1U_mask (e f g h k w : Nat) :
    Nat.land (t1U e f g h k w) w32R = t1Spec e f g h k w := by
  have h1 : Nat.land (t1U e f g h k w) w32R =
      add32R h (Nat.add (bigSigma1U e) (Nat.add {ch_u("e", "f", "g")} (Nat.add k w))) := rfl
  rw [h1, chU_eq]
  rw [← add32R_right_mask h, show Nat.land (Nat.add (bigSigma1U e) (Nat.add (ch e f g) (Nat.add k w))) w32R =
        add32R (bigSigma1U e) (Nat.add (ch e f g) (Nat.add k w)) from rfl]
  rw [← add32R_left_mask (bigSigma1U e), bigSigma1U_mask, add32R_left_mask]
  rw [← add32R_right_mask (bigSigma1 e), show Nat.land (Nat.add (ch e f g) (Nat.add k w)) w32R =
        add32R (ch e f g) (Nat.add k w) from rfl]
  rw [← add32R_right_mask (ch e f g) (Nat.add k w)]
  show add32R h (add32R (bigSigma1 e) (add32R (ch e f g) (add32R k w))) = t1Spec e f g h k w
  simp only [add32R_eq]; rfl

def t2Spec (a b c : Nat) : Nat :=
  add32 (bigSigma0 a) (maj a b c)

theorem t2U_mask (a b c : Nat) :
    Nat.land (t2U a b c) w32R = t2Spec a b c := by
  have h1 : Nat.land (t2U a b c) w32R = add32R (bigSigma0U a) {maj_u("a", "b", "c")} := rfl
  rw [h1, majU_eq, ← add32R_left_mask (bigSigma0U a), bigSigma0U_mask, add32R_left_mask, add32R_eq]
  rfl

theorem add32R_fun : add32R = add32 := funext fun a => funext fun b => add32R_eq a b

theorem mkRoundG_eq : mkRoundG t1U t2U add32 = round := by
  funext s k w
  unfold mkRoundG round
  dsimp only
  have ha : add32 (t1U s.e s.f s.g s.h k w) (t2U s.a s.b s.c) =
      add32 (t1Spec s.e s.f s.g s.h k w) (t2Spec s.a s.b s.c) := by
    rw [← add32R_eq, ← add32R_left_mask (t1U s.e s.f s.g s.h k w), ← add32R_right_mask _ (t2U s.a s.b s.c),
        t1U_mask, t2U_mask, add32R_eq]
  have he : add32 s.d (t1U s.e s.f s.g s.h k w) =
      add32 s.d (t1Spec s.e s.f s.g s.h k w) := by
    rw [← add32R_eq, ← add32R_right_mask s.d (t1U s.e s.f s.g s.h k w), t1U_mask, add32R_eq]
  rw [ha, he]
  rfl

theorem genG_eq : ∀ k w, genG nextWordSpec k w = generate k w
  | 0, _ => rfl
  | k + 1, w => by
      simp only [genG, generate, Window.nextWord, nextWordSpec, genG_eq k]

theorem roundsG_eq : ∀ l s, roundsG round l s = rounds l s
  | [], _ => rfl
  | (k, w) :: rest, s => roundsG_eq rest (round s k w)

theorem initialWindowR_eq (d : Digest) : initialWindowR d = initialWindow d := rfl
theorem ivR_eq : ivR = iv := rfl

theorem drop_last16 (pre : List Nat) (w : Window) :
    (pre ++ w.toList).drop ((pre ++ w.toList).length - 16) = w.toList := by
  simp [Window.toList]

theorem nextWord_eq (w : Window) :
    add32 (add32 (smallSigma1 (w.toList.getD 14 0)) (w.toList.getD 9 0))
      (add32 (smallSigma0 (w.toList.getD 1 0)) (w.toList.getD 0 0)) =
      w.nextWord := by
  rfl

theorem append_push (pre : List Nat) (w : Window) :
    (pre ++ w.toList) ++ [w.nextWord] =
      (pre ++ [w.x0]) ++ (w.push w.nextWord).toList := by
  simp [Window.toList, Window.push]

theorem extend_eq : ∀ k pre w,
    extendW k (pre ++ w.toList) =
      pre ++ w.toList ++ generate k w
  | 0, pre, w => by
      simp [extendW, generate]
  | k + 1, pre, w => by
      rw [extendW, drop_last16, nextWord_eq, append_push]
      rw [extend_eq k (pre ++ [w.x0]) (w.push w.nextWord)]
      simp [generate, Window.toList, Window.push, List.append_assoc]

theorem schedule_correct (d : Digest) :
    fastSchedule d =
      extendW 48 [d.a, d.b, d.c, d.d, d.e, d.f, d.g, d.h,
        0x80000000, 0, 0, 0, 0, 0, 0, 256] := by
  simpa [fastSchedule, initialWindow, Window.toList] using
    (extend_eq 48 [] (initialWindow d)).symm

theorem fastStep_correct (d : Digest) : fastStep d = sha256step d := by
  unfold fastStep sha256step compress
  rw [schedule_correct]

theorem fastStepR_correct (d : Digest) : fastStepR d = sha256step d := by
  rw [fastStepR_eq_unrolled, stepUnrolledG_eq]
  rw [add32R_fun, nextWordR_fun, initialWindowR_eq, ivR_eq]
  unfold stepListG
  rw [genG_eq, mkRoundG_eq, roundsG_eq]
  exact fastStep_correct d

theorem fastStepR_fun : fastStepR = sha256step := funext fastStepR_correct

theorem iterDigestR_eq (step : Digest → Digest) : ∀ t d, iterDigestR step t d = iterDigest step t d
  | 0, _ => rfl
  | t + 1, d => iterDigestR_eq step t (step d)

theorem seedStep32R_eq (x : Nat) : seedStep32R x = seedStep32 x := by
  unfold seedStep32R seedStep32; simp only [hand_eq, hadd_eq, hmul_eq, w32R_eq]

theorem seedDigestR_eq (seed : Nat) : seedDigestR seed = seedDigest seed := by
  unfold seedDigestR seedDigest
  simp only [seedStep32R_eq, hand_eq, w32R_eq]

theorem encodeDigestR_eq (d : Digest) : encodeDigestR d = encodeDigest d := by
  unfold encodeDigestR encodeDigest List.foldl
  have h0 (a : Nat) : 0 * 4294967296 + a = a := by omega
  rw [h0]
  simp only [hadd_eq, hmul_eq, m32R_eq]
  rfl

theorem impl_correct : ∀ n, impl n = sha256Spec n := by
  intro n
  unfold impl sha256Spec iterSha sha256Steps sha256Seed
  rw [encodeDigestR_eq, iterDigestR_eq, fastStepR_fun, seedDigestR_eq]
  simp only [hshr_eq, hand_eq, w32R_eq]

end Submission
"""

DST.write_text(src)
print(f"wrote {DST} ({len(src)} bytes)")
