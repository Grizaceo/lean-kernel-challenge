import Spec

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
def nextWordR (w14 w9 w1 w0 : Nat) : Nat := (Nat.land (Nat.add (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight w14 (nat_lit 17)) (Nat.shiftLeft w14 (nat_lit 15))) (Nat.lor (Nat.shiftRight w14 (nat_lit 19)) (Nat.shiftLeft w14 (nat_lit 13)))) (Nat.shiftRight w14 (nat_lit 10))) w9) (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight w1 (nat_lit 7)) (Nat.shiftLeft w1 (nat_lit 25))) (Nat.lor (Nat.shiftRight w1 (nat_lit 18)) (Nat.shiftLeft w1 (nat_lit 14)))) (Nat.shiftRight w1 (nat_lit 3))) w0)) (nat_lit 4294967295))
def t1U (e f g h k w : Nat) : Nat := (Nat.add h (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight e (nat_lit 6)) (Nat.shiftLeft e (nat_lit 26))) (Nat.lor (Nat.shiftRight e (nat_lit 11)) (Nat.shiftLeft e (nat_lit 21)))) (Nat.lor (Nat.shiftRight e (nat_lit 25)) (Nat.shiftLeft e (nat_lit 7)))) (Nat.add (Nat.xor (Nat.land e f) (Nat.land (Nat.xor e (nat_lit 4294967295)) g)) (Nat.add k w))))
def t2U (a b c : Nat) : Nat := (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight a (nat_lit 2)) (Nat.shiftLeft a (nat_lit 30))) (Nat.lor (Nat.shiftRight a (nat_lit 13)) (Nat.shiftLeft a (nat_lit 19)))) (Nat.lor (Nat.shiftRight a (nat_lit 22)) (Nat.shiftLeft a (nat_lit 10)))) (Nat.xor (Nat.land a (Nat.xor b c)) (Nat.land b c)))

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
  let w_0 := w0.x0; let w_1 := w0.x1; let w_2 := w0.x2; let w_3 := w0.x3
  let w_4 := w0.x4; let w_5 := w0.x5; let w_6 := w0.x6; let w_7 := w0.x7
  let w_8 := w0.x8; let w_9 := w0.x9; let w_10 := w0.x10; let w_11 := w0.x11
  let w_12 := w0.x12; let w_13 := w0.x13; let w_14 := w0.x14; let w_15 := w0.x15
  let a_0 := s0.a; let b_0 := s0.b; let c_0 := s0.c; let d_0 := s0.d
  let e_0 := s0.e; let f_0 := s0.f; let g_0 := s0.g; let h_0 := s0.h
  let t1_0 := t1F e_0 f_0 g_0 h_0 (nat_lit 1116352408) w_0
  let t2_0 := t2F a_0 b_0 c_0
  let na_0 := addF t1_0 t2_0
  let ne_0 := addF d_0 t1_0
  let t1_1 := t1F ne_0 e_0 f_0 g_0 (nat_lit 1899447441) w_1
  let t2_1 := t2F na_0 a_0 b_0
  let na_1 := addF t1_1 t2_1
  let ne_1 := addF c_0 t1_1
  let t1_2 := t1F ne_1 ne_0 e_0 f_0 (nat_lit 3049323471) w_2
  let t2_2 := t2F na_1 na_0 a_0
  let na_2 := addF t1_2 t2_2
  let ne_2 := addF b_0 t1_2
  let t1_3 := t1F ne_2 ne_1 ne_0 e_0 (nat_lit 3921009573) w_3
  let t2_3 := t2F na_2 na_1 na_0
  let na_3 := addF t1_3 t2_3
  let ne_3 := addF a_0 t1_3
  let t1_4 := t1F ne_3 ne_2 ne_1 ne_0 (nat_lit 961987163) w_4
  let t2_4 := t2F na_3 na_2 na_1
  let na_4 := addF t1_4 t2_4
  let ne_4 := addF na_0 t1_4
  let t1_5 := t1F ne_4 ne_3 ne_2 ne_1 (nat_lit 1508970993) w_5
  let t2_5 := t2F na_4 na_3 na_2
  let na_5 := addF t1_5 t2_5
  let ne_5 := addF na_1 t1_5
  let t1_6 := t1F ne_5 ne_4 ne_3 ne_2 (nat_lit 2453635748) w_6
  let t2_6 := t2F na_5 na_4 na_3
  let na_6 := addF t1_6 t2_6
  let ne_6 := addF na_2 t1_6
  let t1_7 := t1F ne_6 ne_5 ne_4 ne_3 (nat_lit 2870763221) w_7
  let t2_7 := t2F na_6 na_5 na_4
  let na_7 := addF t1_7 t2_7
  let ne_7 := addF na_3 t1_7
  let t1_8 := t1F ne_7 ne_6 ne_5 ne_4 (nat_lit 3624381080) w_8
  let t2_8 := t2F na_7 na_6 na_5
  let na_8 := addF t1_8 t2_8
  let ne_8 := addF na_4 t1_8
  let t1_9 := t1F ne_8 ne_7 ne_6 ne_5 (nat_lit 310598401) w_9
  let t2_9 := t2F na_8 na_7 na_6
  let na_9 := addF t1_9 t2_9
  let ne_9 := addF na_5 t1_9
  let t1_10 := t1F ne_9 ne_8 ne_7 ne_6 (nat_lit 607225278) w_10
  let t2_10 := t2F na_9 na_8 na_7
  let na_10 := addF t1_10 t2_10
  let ne_10 := addF na_6 t1_10
  let t1_11 := t1F ne_10 ne_9 ne_8 ne_7 (nat_lit 1426881987) w_11
  let t2_11 := t2F na_10 na_9 na_8
  let na_11 := addF t1_11 t2_11
  let ne_11 := addF na_7 t1_11
  let t1_12 := t1F ne_11 ne_10 ne_9 ne_8 (nat_lit 1925078388) w_12
  let t2_12 := t2F na_11 na_10 na_9
  let na_12 := addF t1_12 t2_12
  let ne_12 := addF na_8 t1_12
  let t1_13 := t1F ne_12 ne_11 ne_10 ne_9 (nat_lit 2162078206) w_13
  let t2_13 := t2F na_12 na_11 na_10
  let na_13 := addF t1_13 t2_13
  let ne_13 := addF na_9 t1_13
  let t1_14 := t1F ne_13 ne_12 ne_11 ne_10 (nat_lit 2614888103) w_14
  let t2_14 := t2F na_13 na_12 na_11
  let na_14 := addF t1_14 t2_14
  let ne_14 := addF na_10 t1_14
  let t1_15 := t1F ne_14 ne_13 ne_12 ne_11 (nat_lit 3248222580) w_15
  let t2_15 := t2F na_14 na_13 na_12
  let na_15 := addF t1_15 t2_15
  let ne_15 := addF na_11 t1_15
  let w_16 := nxt w_14 w_9 w_1 w_0
  let t1_16 := t1F ne_15 ne_14 ne_13 ne_12 (nat_lit 3835390401) w_16
  let t2_16 := t2F na_15 na_14 na_13
  let na_16 := addF t1_16 t2_16
  let ne_16 := addF na_12 t1_16
  let w_17 := nxt w_15 w_10 w_2 w_1
  let t1_17 := t1F ne_16 ne_15 ne_14 ne_13 (nat_lit 4022224774) w_17
  let t2_17 := t2F na_16 na_15 na_14
  let na_17 := addF t1_17 t2_17
  let ne_17 := addF na_13 t1_17
  let w_18 := nxt w_16 w_11 w_3 w_2
  let t1_18 := t1F ne_17 ne_16 ne_15 ne_14 (nat_lit 264347078) w_18
  let t2_18 := t2F na_17 na_16 na_15
  let na_18 := addF t1_18 t2_18
  let ne_18 := addF na_14 t1_18
  let w_19 := nxt w_17 w_12 w_4 w_3
  let t1_19 := t1F ne_18 ne_17 ne_16 ne_15 (nat_lit 604807628) w_19
  let t2_19 := t2F na_18 na_17 na_16
  let na_19 := addF t1_19 t2_19
  let ne_19 := addF na_15 t1_19
  let w_20 := nxt w_18 w_13 w_5 w_4
  let t1_20 := t1F ne_19 ne_18 ne_17 ne_16 (nat_lit 770255983) w_20
  let t2_20 := t2F na_19 na_18 na_17
  let na_20 := addF t1_20 t2_20
  let ne_20 := addF na_16 t1_20
  let w_21 := nxt w_19 w_14 w_6 w_5
  let t1_21 := t1F ne_20 ne_19 ne_18 ne_17 (nat_lit 1249150122) w_21
  let t2_21 := t2F na_20 na_19 na_18
  let na_21 := addF t1_21 t2_21
  let ne_21 := addF na_17 t1_21
  let w_22 := nxt w_20 w_15 w_7 w_6
  let t1_22 := t1F ne_21 ne_20 ne_19 ne_18 (nat_lit 1555081692) w_22
  let t2_22 := t2F na_21 na_20 na_19
  let na_22 := addF t1_22 t2_22
  let ne_22 := addF na_18 t1_22
  let w_23 := nxt w_21 w_16 w_8 w_7
  let t1_23 := t1F ne_22 ne_21 ne_20 ne_19 (nat_lit 1996064986) w_23
  let t2_23 := t2F na_22 na_21 na_20
  let na_23 := addF t1_23 t2_23
  let ne_23 := addF na_19 t1_23
  let w_24 := nxt w_22 w_17 w_9 w_8
  let t1_24 := t1F ne_23 ne_22 ne_21 ne_20 (nat_lit 2554220882) w_24
  let t2_24 := t2F na_23 na_22 na_21
  let na_24 := addF t1_24 t2_24
  let ne_24 := addF na_20 t1_24
  let w_25 := nxt w_23 w_18 w_10 w_9
  let t1_25 := t1F ne_24 ne_23 ne_22 ne_21 (nat_lit 2821834349) w_25
  let t2_25 := t2F na_24 na_23 na_22
  let na_25 := addF t1_25 t2_25
  let ne_25 := addF na_21 t1_25
  let w_26 := nxt w_24 w_19 w_11 w_10
  let t1_26 := t1F ne_25 ne_24 ne_23 ne_22 (nat_lit 2952996808) w_26
  let t2_26 := t2F na_25 na_24 na_23
  let na_26 := addF t1_26 t2_26
  let ne_26 := addF na_22 t1_26
  let w_27 := nxt w_25 w_20 w_12 w_11
  let t1_27 := t1F ne_26 ne_25 ne_24 ne_23 (nat_lit 3210313671) w_27
  let t2_27 := t2F na_26 na_25 na_24
  let na_27 := addF t1_27 t2_27
  let ne_27 := addF na_23 t1_27
  let w_28 := nxt w_26 w_21 w_13 w_12
  let t1_28 := t1F ne_27 ne_26 ne_25 ne_24 (nat_lit 3336571891) w_28
  let t2_28 := t2F na_27 na_26 na_25
  let na_28 := addF t1_28 t2_28
  let ne_28 := addF na_24 t1_28
  let w_29 := nxt w_27 w_22 w_14 w_13
  let t1_29 := t1F ne_28 ne_27 ne_26 ne_25 (nat_lit 3584528711) w_29
  let t2_29 := t2F na_28 na_27 na_26
  let na_29 := addF t1_29 t2_29
  let ne_29 := addF na_25 t1_29
  let w_30 := nxt w_28 w_23 w_15 w_14
  let t1_30 := t1F ne_29 ne_28 ne_27 ne_26 (nat_lit 113926993) w_30
  let t2_30 := t2F na_29 na_28 na_27
  let na_30 := addF t1_30 t2_30
  let ne_30 := addF na_26 t1_30
  let w_31 := nxt w_29 w_24 w_16 w_15
  let t1_31 := t1F ne_30 ne_29 ne_28 ne_27 (nat_lit 338241895) w_31
  let t2_31 := t2F na_30 na_29 na_28
  let na_31 := addF t1_31 t2_31
  let ne_31 := addF na_27 t1_31
  let w_32 := nxt w_30 w_25 w_17 w_16
  let t1_32 := t1F ne_31 ne_30 ne_29 ne_28 (nat_lit 666307205) w_32
  let t2_32 := t2F na_31 na_30 na_29
  let na_32 := addF t1_32 t2_32
  let ne_32 := addF na_28 t1_32
  let w_33 := nxt w_31 w_26 w_18 w_17
  let t1_33 := t1F ne_32 ne_31 ne_30 ne_29 (nat_lit 773529912) w_33
  let t2_33 := t2F na_32 na_31 na_30
  let na_33 := addF t1_33 t2_33
  let ne_33 := addF na_29 t1_33
  let w_34 := nxt w_32 w_27 w_19 w_18
  let t1_34 := t1F ne_33 ne_32 ne_31 ne_30 (nat_lit 1294757372) w_34
  let t2_34 := t2F na_33 na_32 na_31
  let na_34 := addF t1_34 t2_34
  let ne_34 := addF na_30 t1_34
  let w_35 := nxt w_33 w_28 w_20 w_19
  let t1_35 := t1F ne_34 ne_33 ne_32 ne_31 (nat_lit 1396182291) w_35
  let t2_35 := t2F na_34 na_33 na_32
  let na_35 := addF t1_35 t2_35
  let ne_35 := addF na_31 t1_35
  let w_36 := nxt w_34 w_29 w_21 w_20
  let t1_36 := t1F ne_35 ne_34 ne_33 ne_32 (nat_lit 1695183700) w_36
  let t2_36 := t2F na_35 na_34 na_33
  let na_36 := addF t1_36 t2_36
  let ne_36 := addF na_32 t1_36
  let w_37 := nxt w_35 w_30 w_22 w_21
  let t1_37 := t1F ne_36 ne_35 ne_34 ne_33 (nat_lit 1986661051) w_37
  let t2_37 := t2F na_36 na_35 na_34
  let na_37 := addF t1_37 t2_37
  let ne_37 := addF na_33 t1_37
  let w_38 := nxt w_36 w_31 w_23 w_22
  let t1_38 := t1F ne_37 ne_36 ne_35 ne_34 (nat_lit 2177026350) w_38
  let t2_38 := t2F na_37 na_36 na_35
  let na_38 := addF t1_38 t2_38
  let ne_38 := addF na_34 t1_38
  let w_39 := nxt w_37 w_32 w_24 w_23
  let t1_39 := t1F ne_38 ne_37 ne_36 ne_35 (nat_lit 2456956037) w_39
  let t2_39 := t2F na_38 na_37 na_36
  let na_39 := addF t1_39 t2_39
  let ne_39 := addF na_35 t1_39
  let w_40 := nxt w_38 w_33 w_25 w_24
  let t1_40 := t1F ne_39 ne_38 ne_37 ne_36 (nat_lit 2730485921) w_40
  let t2_40 := t2F na_39 na_38 na_37
  let na_40 := addF t1_40 t2_40
  let ne_40 := addF na_36 t1_40
  let w_41 := nxt w_39 w_34 w_26 w_25
  let t1_41 := t1F ne_40 ne_39 ne_38 ne_37 (nat_lit 2820302411) w_41
  let t2_41 := t2F na_40 na_39 na_38
  let na_41 := addF t1_41 t2_41
  let ne_41 := addF na_37 t1_41
  let w_42 := nxt w_40 w_35 w_27 w_26
  let t1_42 := t1F ne_41 ne_40 ne_39 ne_38 (nat_lit 3259730800) w_42
  let t2_42 := t2F na_41 na_40 na_39
  let na_42 := addF t1_42 t2_42
  let ne_42 := addF na_38 t1_42
  let w_43 := nxt w_41 w_36 w_28 w_27
  let t1_43 := t1F ne_42 ne_41 ne_40 ne_39 (nat_lit 3345764771) w_43
  let t2_43 := t2F na_42 na_41 na_40
  let na_43 := addF t1_43 t2_43
  let ne_43 := addF na_39 t1_43
  let w_44 := nxt w_42 w_37 w_29 w_28
  let t1_44 := t1F ne_43 ne_42 ne_41 ne_40 (nat_lit 3516065817) w_44
  let t2_44 := t2F na_43 na_42 na_41
  let na_44 := addF t1_44 t2_44
  let ne_44 := addF na_40 t1_44
  let w_45 := nxt w_43 w_38 w_30 w_29
  let t1_45 := t1F ne_44 ne_43 ne_42 ne_41 (nat_lit 3600352804) w_45
  let t2_45 := t2F na_44 na_43 na_42
  let na_45 := addF t1_45 t2_45
  let ne_45 := addF na_41 t1_45
  let w_46 := nxt w_44 w_39 w_31 w_30
  let t1_46 := t1F ne_45 ne_44 ne_43 ne_42 (nat_lit 4094571909) w_46
  let t2_46 := t2F na_45 na_44 na_43
  let na_46 := addF t1_46 t2_46
  let ne_46 := addF na_42 t1_46
  let w_47 := nxt w_45 w_40 w_32 w_31
  let t1_47 := t1F ne_46 ne_45 ne_44 ne_43 (nat_lit 275423344) w_47
  let t2_47 := t2F na_46 na_45 na_44
  let na_47 := addF t1_47 t2_47
  let ne_47 := addF na_43 t1_47
  let w_48 := nxt w_46 w_41 w_33 w_32
  let t1_48 := t1F ne_47 ne_46 ne_45 ne_44 (nat_lit 430227734) w_48
  let t2_48 := t2F na_47 na_46 na_45
  let na_48 := addF t1_48 t2_48
  let ne_48 := addF na_44 t1_48
  let w_49 := nxt w_47 w_42 w_34 w_33
  let t1_49 := t1F ne_48 ne_47 ne_46 ne_45 (nat_lit 506948616) w_49
  let t2_49 := t2F na_48 na_47 na_46
  let na_49 := addF t1_49 t2_49
  let ne_49 := addF na_45 t1_49
  let w_50 := nxt w_48 w_43 w_35 w_34
  let t1_50 := t1F ne_49 ne_48 ne_47 ne_46 (nat_lit 659060556) w_50
  let t2_50 := t2F na_49 na_48 na_47
  let na_50 := addF t1_50 t2_50
  let ne_50 := addF na_46 t1_50
  let w_51 := nxt w_49 w_44 w_36 w_35
  let t1_51 := t1F ne_50 ne_49 ne_48 ne_47 (nat_lit 883997877) w_51
  let t2_51 := t2F na_50 na_49 na_48
  let na_51 := addF t1_51 t2_51
  let ne_51 := addF na_47 t1_51
  let w_52 := nxt w_50 w_45 w_37 w_36
  let t1_52 := t1F ne_51 ne_50 ne_49 ne_48 (nat_lit 958139571) w_52
  let t2_52 := t2F na_51 na_50 na_49
  let na_52 := addF t1_52 t2_52
  let ne_52 := addF na_48 t1_52
  let w_53 := nxt w_51 w_46 w_38 w_37
  let t1_53 := t1F ne_52 ne_51 ne_50 ne_49 (nat_lit 1322822218) w_53
  let t2_53 := t2F na_52 na_51 na_50
  let na_53 := addF t1_53 t2_53
  let ne_53 := addF na_49 t1_53
  let w_54 := nxt w_52 w_47 w_39 w_38
  let t1_54 := t1F ne_53 ne_52 ne_51 ne_50 (nat_lit 1537002063) w_54
  let t2_54 := t2F na_53 na_52 na_51
  let na_54 := addF t1_54 t2_54
  let ne_54 := addF na_50 t1_54
  let w_55 := nxt w_53 w_48 w_40 w_39
  let t1_55 := t1F ne_54 ne_53 ne_52 ne_51 (nat_lit 1747873779) w_55
  let t2_55 := t2F na_54 na_53 na_52
  let na_55 := addF t1_55 t2_55
  let ne_55 := addF na_51 t1_55
  let w_56 := nxt w_54 w_49 w_41 w_40
  let t1_56 := t1F ne_55 ne_54 ne_53 ne_52 (nat_lit 1955562222) w_56
  let t2_56 := t2F na_55 na_54 na_53
  let na_56 := addF t1_56 t2_56
  let ne_56 := addF na_52 t1_56
  let w_57 := nxt w_55 w_50 w_42 w_41
  let t1_57 := t1F ne_56 ne_55 ne_54 ne_53 (nat_lit 2024104815) w_57
  let t2_57 := t2F na_56 na_55 na_54
  let na_57 := addF t1_57 t2_57
  let ne_57 := addF na_53 t1_57
  let w_58 := nxt w_56 w_51 w_43 w_42
  let t1_58 := t1F ne_57 ne_56 ne_55 ne_54 (nat_lit 2227730452) w_58
  let t2_58 := t2F na_57 na_56 na_55
  let na_58 := addF t1_58 t2_58
  let ne_58 := addF na_54 t1_58
  let w_59 := nxt w_57 w_52 w_44 w_43
  let t1_59 := t1F ne_58 ne_57 ne_56 ne_55 (nat_lit 2361852424) w_59
  let t2_59 := t2F na_58 na_57 na_56
  let na_59 := addF t1_59 t2_59
  let ne_59 := addF na_55 t1_59
  let w_60 := nxt w_58 w_53 w_45 w_44
  let t1_60 := t1F ne_59 ne_58 ne_57 ne_56 (nat_lit 2428436474) w_60
  let t2_60 := t2F na_59 na_58 na_57
  let na_60 := addF t1_60 t2_60
  let ne_60 := addF na_56 t1_60
  let w_61 := nxt w_59 w_54 w_46 w_45
  let t1_61 := t1F ne_60 ne_59 ne_58 ne_57 (nat_lit 2756734187) w_61
  let t2_61 := t2F na_60 na_59 na_58
  let na_61 := addF t1_61 t2_61
  let ne_61 := addF na_57 t1_61
  let w_62 := nxt w_60 w_55 w_47 w_46
  let t1_62 := t1F ne_61 ne_60 ne_59 ne_58 (nat_lit 3204031479) w_62
  let t2_62 := t2F na_61 na_60 na_59
  let na_62 := addF t1_62 t2_62
  let ne_62 := addF na_58 t1_62
  let w_63 := nxt w_61 w_56 w_48 w_47
  let t1_63 := t1F ne_62 ne_61 ne_60 ne_59 (nat_lit 3329325298) w_63
  let t2_63 := t2F na_62 na_61 na_60
  let na_63 := addF t1_63 t2_63
  let ne_63 := addF na_59 t1_63
  ⟨addF s0.a na_63, addF s0.b na_62, addF s0.c na_61, addF s0.d na_60, addF s0.e ne_63, addF s0.f ne_62, addF s0.g ne_61, addF s0.h ne_60⟩

theorem stepUnrolledG_eq (t1F : Nat → Nat → Nat → Nat → Nat → Nat → Nat)
    (t2F : Nat → Nat → Nat → Nat) (addF : Nat → Nat → Nat)
    (nxt : Nat → Nat → Nat → Nat → Nat) (w0 : Window) (s0 : Digest) :
    stepUnrolledG t1F t2F addF nxt w0 s0 = stepListG t1F t2F addF nxt w0 s0 := rfl



def fastStepR (d : Digest) : Digest :=
  let w_0 := d.a
  let t1_0 := (Nat.add (nat_lit 1541459225) (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight (nat_lit 1359893119) (nat_lit 6)) (Nat.shiftLeft (nat_lit 1359893119) (nat_lit 26))) (Nat.lor (Nat.shiftRight (nat_lit 1359893119) (nat_lit 11)) (Nat.shiftLeft (nat_lit 1359893119) (nat_lit 21)))) (Nat.lor (Nat.shiftRight (nat_lit 1359893119) (nat_lit 25)) (Nat.shiftLeft (nat_lit 1359893119) (nat_lit 7)))) (Nat.add (Nat.xor (Nat.land (nat_lit 1359893119) (nat_lit 2600822924)) (Nat.land (Nat.xor (nat_lit 1359893119) (nat_lit 4294967295)) (nat_lit 528734635))) (Nat.add (nat_lit 1116352408) w_0))))
  let na_0 := (Nat.land (Nat.add t1_0 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight (nat_lit 1779033703) (nat_lit 2)) (Nat.shiftLeft (nat_lit 1779033703) (nat_lit 30))) (Nat.lor (Nat.shiftRight (nat_lit 1779033703) (nat_lit 13)) (Nat.shiftLeft (nat_lit 1779033703) (nat_lit 19)))) (Nat.lor (Nat.shiftRight (nat_lit 1779033703) (nat_lit 22)) (Nat.shiftLeft (nat_lit 1779033703) (nat_lit 10)))) (Nat.xor (Nat.land (nat_lit 1779033703) (Nat.xor (nat_lit 3144134277) (nat_lit 1013904242))) (Nat.land (nat_lit 3144134277) (nat_lit 1013904242))))) (nat_lit 4294967295))
  let ne_0 := (Nat.land (Nat.add (nat_lit 2773480762) t1_0) (nat_lit 4294967295))
  let w_1 := d.b
  let t1_1 := (Nat.add (nat_lit 528734635) (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight ne_0 (nat_lit 6)) (Nat.shiftLeft ne_0 (nat_lit 26))) (Nat.lor (Nat.shiftRight ne_0 (nat_lit 11)) (Nat.shiftLeft ne_0 (nat_lit 21)))) (Nat.lor (Nat.shiftRight ne_0 (nat_lit 25)) (Nat.shiftLeft ne_0 (nat_lit 7)))) (Nat.add (Nat.xor (Nat.land ne_0 (nat_lit 1359893119)) (Nat.land (Nat.xor ne_0 (nat_lit 4294967295)) (nat_lit 2600822924))) (Nat.add (nat_lit 1899447441) w_1))))
  let na_1 := (Nat.land (Nat.add t1_1 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight na_0 (nat_lit 2)) (Nat.shiftLeft na_0 (nat_lit 30))) (Nat.lor (Nat.shiftRight na_0 (nat_lit 13)) (Nat.shiftLeft na_0 (nat_lit 19)))) (Nat.lor (Nat.shiftRight na_0 (nat_lit 22)) (Nat.shiftLeft na_0 (nat_lit 10)))) (Nat.xor (Nat.land na_0 (Nat.xor (nat_lit 1779033703) (nat_lit 3144134277))) (Nat.land (nat_lit 1779033703) (nat_lit 3144134277))))) (nat_lit 4294967295))
  let ne_1 := (Nat.land (Nat.add (nat_lit 1013904242) t1_1) (nat_lit 4294967295))
  let w_2 := d.c
  let t1_2 := (Nat.add (nat_lit 2600822924) (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight ne_1 (nat_lit 6)) (Nat.shiftLeft ne_1 (nat_lit 26))) (Nat.lor (Nat.shiftRight ne_1 (nat_lit 11)) (Nat.shiftLeft ne_1 (nat_lit 21)))) (Nat.lor (Nat.shiftRight ne_1 (nat_lit 25)) (Nat.shiftLeft ne_1 (nat_lit 7)))) (Nat.add (Nat.xor (Nat.land ne_1 ne_0) (Nat.land (Nat.xor ne_1 (nat_lit 4294967295)) (nat_lit 1359893119))) (Nat.add (nat_lit 3049323471) w_2))))
  let na_2 := (Nat.land (Nat.add t1_2 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight na_1 (nat_lit 2)) (Nat.shiftLeft na_1 (nat_lit 30))) (Nat.lor (Nat.shiftRight na_1 (nat_lit 13)) (Nat.shiftLeft na_1 (nat_lit 19)))) (Nat.lor (Nat.shiftRight na_1 (nat_lit 22)) (Nat.shiftLeft na_1 (nat_lit 10)))) (Nat.xor (Nat.land na_1 (Nat.xor na_0 (nat_lit 1779033703))) (Nat.land na_0 (nat_lit 1779033703))))) (nat_lit 4294967295))
  let ne_2 := (Nat.land (Nat.add (nat_lit 3144134277) t1_2) (nat_lit 4294967295))
  let w_3 := d.d
  let t1_3 := (Nat.add (nat_lit 1359893119) (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight ne_2 (nat_lit 6)) (Nat.shiftLeft ne_2 (nat_lit 26))) (Nat.lor (Nat.shiftRight ne_2 (nat_lit 11)) (Nat.shiftLeft ne_2 (nat_lit 21)))) (Nat.lor (Nat.shiftRight ne_2 (nat_lit 25)) (Nat.shiftLeft ne_2 (nat_lit 7)))) (Nat.add (Nat.xor (Nat.land ne_2 ne_1) (Nat.land (Nat.xor ne_2 (nat_lit 4294967295)) ne_0)) (Nat.add (nat_lit 3921009573) w_3))))
  let na_3 := (Nat.land (Nat.add t1_3 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight na_2 (nat_lit 2)) (Nat.shiftLeft na_2 (nat_lit 30))) (Nat.lor (Nat.shiftRight na_2 (nat_lit 13)) (Nat.shiftLeft na_2 (nat_lit 19)))) (Nat.lor (Nat.shiftRight na_2 (nat_lit 22)) (Nat.shiftLeft na_2 (nat_lit 10)))) (Nat.xor (Nat.land na_2 (Nat.xor na_1 na_0)) (Nat.land na_1 na_0)))) (nat_lit 4294967295))
  let ne_3 := (Nat.land (Nat.add (nat_lit 1779033703) t1_3) (nat_lit 4294967295))
  let w_4 := d.e
  let t1_4 := (Nat.add ne_0 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight ne_3 (nat_lit 6)) (Nat.shiftLeft ne_3 (nat_lit 26))) (Nat.lor (Nat.shiftRight ne_3 (nat_lit 11)) (Nat.shiftLeft ne_3 (nat_lit 21)))) (Nat.lor (Nat.shiftRight ne_3 (nat_lit 25)) (Nat.shiftLeft ne_3 (nat_lit 7)))) (Nat.add (Nat.xor (Nat.land ne_3 ne_2) (Nat.land (Nat.xor ne_3 (nat_lit 4294967295)) ne_1)) (Nat.add (nat_lit 961987163) w_4))))
  let na_4 := (Nat.land (Nat.add t1_4 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight na_3 (nat_lit 2)) (Nat.shiftLeft na_3 (nat_lit 30))) (Nat.lor (Nat.shiftRight na_3 (nat_lit 13)) (Nat.shiftLeft na_3 (nat_lit 19)))) (Nat.lor (Nat.shiftRight na_3 (nat_lit 22)) (Nat.shiftLeft na_3 (nat_lit 10)))) (Nat.xor (Nat.land na_3 (Nat.xor na_2 na_1)) (Nat.land na_2 na_1)))) (nat_lit 4294967295))
  let ne_4 := (Nat.land (Nat.add na_0 t1_4) (nat_lit 4294967295))
  let w_5 := d.f
  let t1_5 := (Nat.add ne_1 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight ne_4 (nat_lit 6)) (Nat.shiftLeft ne_4 (nat_lit 26))) (Nat.lor (Nat.shiftRight ne_4 (nat_lit 11)) (Nat.shiftLeft ne_4 (nat_lit 21)))) (Nat.lor (Nat.shiftRight ne_4 (nat_lit 25)) (Nat.shiftLeft ne_4 (nat_lit 7)))) (Nat.add (Nat.xor (Nat.land ne_4 ne_3) (Nat.land (Nat.xor ne_4 (nat_lit 4294967295)) ne_2)) (Nat.add (nat_lit 1508970993) w_5))))
  let na_5 := (Nat.land (Nat.add t1_5 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight na_4 (nat_lit 2)) (Nat.shiftLeft na_4 (nat_lit 30))) (Nat.lor (Nat.shiftRight na_4 (nat_lit 13)) (Nat.shiftLeft na_4 (nat_lit 19)))) (Nat.lor (Nat.shiftRight na_4 (nat_lit 22)) (Nat.shiftLeft na_4 (nat_lit 10)))) (Nat.xor (Nat.land na_4 (Nat.xor na_3 na_2)) (Nat.land na_3 na_2)))) (nat_lit 4294967295))
  let ne_5 := (Nat.land (Nat.add na_1 t1_5) (nat_lit 4294967295))
  let w_6 := d.g
  let t1_6 := (Nat.add ne_2 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight ne_5 (nat_lit 6)) (Nat.shiftLeft ne_5 (nat_lit 26))) (Nat.lor (Nat.shiftRight ne_5 (nat_lit 11)) (Nat.shiftLeft ne_5 (nat_lit 21)))) (Nat.lor (Nat.shiftRight ne_5 (nat_lit 25)) (Nat.shiftLeft ne_5 (nat_lit 7)))) (Nat.add (Nat.xor (Nat.land ne_5 ne_4) (Nat.land (Nat.xor ne_5 (nat_lit 4294967295)) ne_3)) (Nat.add (nat_lit 2453635748) w_6))))
  let na_6 := (Nat.land (Nat.add t1_6 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight na_5 (nat_lit 2)) (Nat.shiftLeft na_5 (nat_lit 30))) (Nat.lor (Nat.shiftRight na_5 (nat_lit 13)) (Nat.shiftLeft na_5 (nat_lit 19)))) (Nat.lor (Nat.shiftRight na_5 (nat_lit 22)) (Nat.shiftLeft na_5 (nat_lit 10)))) (Nat.xor (Nat.land na_5 (Nat.xor na_4 na_3)) (Nat.land na_4 na_3)))) (nat_lit 4294967295))
  let ne_6 := (Nat.land (Nat.add na_2 t1_6) (nat_lit 4294967295))
  let w_7 := d.h
  let t1_7 := (Nat.add ne_3 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight ne_6 (nat_lit 6)) (Nat.shiftLeft ne_6 (nat_lit 26))) (Nat.lor (Nat.shiftRight ne_6 (nat_lit 11)) (Nat.shiftLeft ne_6 (nat_lit 21)))) (Nat.lor (Nat.shiftRight ne_6 (nat_lit 25)) (Nat.shiftLeft ne_6 (nat_lit 7)))) (Nat.add (Nat.xor (Nat.land ne_6 ne_5) (Nat.land (Nat.xor ne_6 (nat_lit 4294967295)) ne_4)) (Nat.add (nat_lit 2870763221) w_7))))
  let na_7 := (Nat.land (Nat.add t1_7 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight na_6 (nat_lit 2)) (Nat.shiftLeft na_6 (nat_lit 30))) (Nat.lor (Nat.shiftRight na_6 (nat_lit 13)) (Nat.shiftLeft na_6 (nat_lit 19)))) (Nat.lor (Nat.shiftRight na_6 (nat_lit 22)) (Nat.shiftLeft na_6 (nat_lit 10)))) (Nat.xor (Nat.land na_6 (Nat.xor na_5 na_4)) (Nat.land na_5 na_4)))) (nat_lit 4294967295))
  let ne_7 := (Nat.land (Nat.add na_3 t1_7) (nat_lit 4294967295))
  let t1_8 := (Nat.add ne_4 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight ne_7 (nat_lit 6)) (Nat.shiftLeft ne_7 (nat_lit 26))) (Nat.lor (Nat.shiftRight ne_7 (nat_lit 11)) (Nat.shiftLeft ne_7 (nat_lit 21)))) (Nat.lor (Nat.shiftRight ne_7 (nat_lit 25)) (Nat.shiftLeft ne_7 (nat_lit 7)))) (Nat.add (Nat.xor (Nat.land ne_7 ne_6) (Nat.land (Nat.xor ne_7 (nat_lit 4294967295)) ne_5)) (Nat.add (nat_lit 3624381080) (nat_lit 0x80000000)))))
  let na_8 := (Nat.land (Nat.add t1_8 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight na_7 (nat_lit 2)) (Nat.shiftLeft na_7 (nat_lit 30))) (Nat.lor (Nat.shiftRight na_7 (nat_lit 13)) (Nat.shiftLeft na_7 (nat_lit 19)))) (Nat.lor (Nat.shiftRight na_7 (nat_lit 22)) (Nat.shiftLeft na_7 (nat_lit 10)))) (Nat.xor (Nat.land na_7 (Nat.xor na_6 na_5)) (Nat.land na_6 na_5)))) (nat_lit 4294967295))
  let ne_8 := (Nat.land (Nat.add na_4 t1_8) (nat_lit 4294967295))
  let t1_9 := (Nat.add ne_5 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight ne_8 (nat_lit 6)) (Nat.shiftLeft ne_8 (nat_lit 26))) (Nat.lor (Nat.shiftRight ne_8 (nat_lit 11)) (Nat.shiftLeft ne_8 (nat_lit 21)))) (Nat.lor (Nat.shiftRight ne_8 (nat_lit 25)) (Nat.shiftLeft ne_8 (nat_lit 7)))) (Nat.add (Nat.xor (Nat.land ne_8 ne_7) (Nat.land (Nat.xor ne_8 (nat_lit 4294967295)) ne_6)) (Nat.add (nat_lit 310598401) (nat_lit 0)))))
  let na_9 := (Nat.land (Nat.add t1_9 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight na_8 (nat_lit 2)) (Nat.shiftLeft na_8 (nat_lit 30))) (Nat.lor (Nat.shiftRight na_8 (nat_lit 13)) (Nat.shiftLeft na_8 (nat_lit 19)))) (Nat.lor (Nat.shiftRight na_8 (nat_lit 22)) (Nat.shiftLeft na_8 (nat_lit 10)))) (Nat.xor (Nat.land na_8 (Nat.xor na_7 na_6)) (Nat.land na_7 na_6)))) (nat_lit 4294967295))
  let ne_9 := (Nat.land (Nat.add na_5 t1_9) (nat_lit 4294967295))
  let t1_10 := (Nat.add ne_6 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight ne_9 (nat_lit 6)) (Nat.shiftLeft ne_9 (nat_lit 26))) (Nat.lor (Nat.shiftRight ne_9 (nat_lit 11)) (Nat.shiftLeft ne_9 (nat_lit 21)))) (Nat.lor (Nat.shiftRight ne_9 (nat_lit 25)) (Nat.shiftLeft ne_9 (nat_lit 7)))) (Nat.add (Nat.xor (Nat.land ne_9 ne_8) (Nat.land (Nat.xor ne_9 (nat_lit 4294967295)) ne_7)) (Nat.add (nat_lit 607225278) (nat_lit 0)))))
  let na_10 := (Nat.land (Nat.add t1_10 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight na_9 (nat_lit 2)) (Nat.shiftLeft na_9 (nat_lit 30))) (Nat.lor (Nat.shiftRight na_9 (nat_lit 13)) (Nat.shiftLeft na_9 (nat_lit 19)))) (Nat.lor (Nat.shiftRight na_9 (nat_lit 22)) (Nat.shiftLeft na_9 (nat_lit 10)))) (Nat.xor (Nat.land na_9 (Nat.xor na_8 na_7)) (Nat.land na_8 na_7)))) (nat_lit 4294967295))
  let ne_10 := (Nat.land (Nat.add na_6 t1_10) (nat_lit 4294967295))
  let t1_11 := (Nat.add ne_7 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight ne_10 (nat_lit 6)) (Nat.shiftLeft ne_10 (nat_lit 26))) (Nat.lor (Nat.shiftRight ne_10 (nat_lit 11)) (Nat.shiftLeft ne_10 (nat_lit 21)))) (Nat.lor (Nat.shiftRight ne_10 (nat_lit 25)) (Nat.shiftLeft ne_10 (nat_lit 7)))) (Nat.add (Nat.xor (Nat.land ne_10 ne_9) (Nat.land (Nat.xor ne_10 (nat_lit 4294967295)) ne_8)) (Nat.add (nat_lit 1426881987) (nat_lit 0)))))
  let na_11 := (Nat.land (Nat.add t1_11 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight na_10 (nat_lit 2)) (Nat.shiftLeft na_10 (nat_lit 30))) (Nat.lor (Nat.shiftRight na_10 (nat_lit 13)) (Nat.shiftLeft na_10 (nat_lit 19)))) (Nat.lor (Nat.shiftRight na_10 (nat_lit 22)) (Nat.shiftLeft na_10 (nat_lit 10)))) (Nat.xor (Nat.land na_10 (Nat.xor na_9 na_8)) (Nat.land na_9 na_8)))) (nat_lit 4294967295))
  let ne_11 := (Nat.land (Nat.add na_7 t1_11) (nat_lit 4294967295))
  let t1_12 := (Nat.add ne_8 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight ne_11 (nat_lit 6)) (Nat.shiftLeft ne_11 (nat_lit 26))) (Nat.lor (Nat.shiftRight ne_11 (nat_lit 11)) (Nat.shiftLeft ne_11 (nat_lit 21)))) (Nat.lor (Nat.shiftRight ne_11 (nat_lit 25)) (Nat.shiftLeft ne_11 (nat_lit 7)))) (Nat.add (Nat.xor (Nat.land ne_11 ne_10) (Nat.land (Nat.xor ne_11 (nat_lit 4294967295)) ne_9)) (Nat.add (nat_lit 1925078388) (nat_lit 0)))))
  let na_12 := (Nat.land (Nat.add t1_12 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight na_11 (nat_lit 2)) (Nat.shiftLeft na_11 (nat_lit 30))) (Nat.lor (Nat.shiftRight na_11 (nat_lit 13)) (Nat.shiftLeft na_11 (nat_lit 19)))) (Nat.lor (Nat.shiftRight na_11 (nat_lit 22)) (Nat.shiftLeft na_11 (nat_lit 10)))) (Nat.xor (Nat.land na_11 (Nat.xor na_10 na_9)) (Nat.land na_10 na_9)))) (nat_lit 4294967295))
  let ne_12 := (Nat.land (Nat.add na_8 t1_12) (nat_lit 4294967295))
  let t1_13 := (Nat.add ne_9 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight ne_12 (nat_lit 6)) (Nat.shiftLeft ne_12 (nat_lit 26))) (Nat.lor (Nat.shiftRight ne_12 (nat_lit 11)) (Nat.shiftLeft ne_12 (nat_lit 21)))) (Nat.lor (Nat.shiftRight ne_12 (nat_lit 25)) (Nat.shiftLeft ne_12 (nat_lit 7)))) (Nat.add (Nat.xor (Nat.land ne_12 ne_11) (Nat.land (Nat.xor ne_12 (nat_lit 4294967295)) ne_10)) (Nat.add (nat_lit 2162078206) (nat_lit 0)))))
  let na_13 := (Nat.land (Nat.add t1_13 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight na_12 (nat_lit 2)) (Nat.shiftLeft na_12 (nat_lit 30))) (Nat.lor (Nat.shiftRight na_12 (nat_lit 13)) (Nat.shiftLeft na_12 (nat_lit 19)))) (Nat.lor (Nat.shiftRight na_12 (nat_lit 22)) (Nat.shiftLeft na_12 (nat_lit 10)))) (Nat.xor (Nat.land na_12 (Nat.xor na_11 na_10)) (Nat.land na_11 na_10)))) (nat_lit 4294967295))
  let ne_13 := (Nat.land (Nat.add na_9 t1_13) (nat_lit 4294967295))
  let t1_14 := (Nat.add ne_10 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight ne_13 (nat_lit 6)) (Nat.shiftLeft ne_13 (nat_lit 26))) (Nat.lor (Nat.shiftRight ne_13 (nat_lit 11)) (Nat.shiftLeft ne_13 (nat_lit 21)))) (Nat.lor (Nat.shiftRight ne_13 (nat_lit 25)) (Nat.shiftLeft ne_13 (nat_lit 7)))) (Nat.add (Nat.xor (Nat.land ne_13 ne_12) (Nat.land (Nat.xor ne_13 (nat_lit 4294967295)) ne_11)) (Nat.add (nat_lit 2614888103) (nat_lit 0)))))
  let na_14 := (Nat.land (Nat.add t1_14 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight na_13 (nat_lit 2)) (Nat.shiftLeft na_13 (nat_lit 30))) (Nat.lor (Nat.shiftRight na_13 (nat_lit 13)) (Nat.shiftLeft na_13 (nat_lit 19)))) (Nat.lor (Nat.shiftRight na_13 (nat_lit 22)) (Nat.shiftLeft na_13 (nat_lit 10)))) (Nat.xor (Nat.land na_13 (Nat.xor na_12 na_11)) (Nat.land na_12 na_11)))) (nat_lit 4294967295))
  let ne_14 := (Nat.land (Nat.add na_10 t1_14) (nat_lit 4294967295))
  let t1_15 := (Nat.add ne_11 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight ne_14 (nat_lit 6)) (Nat.shiftLeft ne_14 (nat_lit 26))) (Nat.lor (Nat.shiftRight ne_14 (nat_lit 11)) (Nat.shiftLeft ne_14 (nat_lit 21)))) (Nat.lor (Nat.shiftRight ne_14 (nat_lit 25)) (Nat.shiftLeft ne_14 (nat_lit 7)))) (Nat.add (Nat.xor (Nat.land ne_14 ne_13) (Nat.land (Nat.xor ne_14 (nat_lit 4294967295)) ne_12)) (Nat.add (nat_lit 3248222580) (nat_lit 256)))))
  let na_15 := (Nat.land (Nat.add t1_15 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight na_14 (nat_lit 2)) (Nat.shiftLeft na_14 (nat_lit 30))) (Nat.lor (Nat.shiftRight na_14 (nat_lit 13)) (Nat.shiftLeft na_14 (nat_lit 19)))) (Nat.lor (Nat.shiftRight na_14 (nat_lit 22)) (Nat.shiftLeft na_14 (nat_lit 10)))) (Nat.xor (Nat.land na_14 (Nat.xor na_13 na_12)) (Nat.land na_13 na_12)))) (nat_lit 4294967295))
  let ne_15 := (Nat.land (Nat.add na_11 t1_15) (nat_lit 4294967295))
  let w_16 := (Nat.land (Nat.add (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight (nat_lit 0) (nat_lit 17)) (Nat.shiftLeft (nat_lit 0) (nat_lit 15))) (Nat.lor (Nat.shiftRight (nat_lit 0) (nat_lit 19)) (Nat.shiftLeft (nat_lit 0) (nat_lit 13)))) (Nat.shiftRight (nat_lit 0) (nat_lit 10))) (nat_lit 0)) (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight w_1 (nat_lit 7)) (Nat.shiftLeft w_1 (nat_lit 25))) (Nat.lor (Nat.shiftRight w_1 (nat_lit 18)) (Nat.shiftLeft w_1 (nat_lit 14)))) (Nat.shiftRight w_1 (nat_lit 3))) w_0)) (nat_lit 4294967295))
  let t1_16 := (Nat.add ne_12 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight ne_15 (nat_lit 6)) (Nat.shiftLeft ne_15 (nat_lit 26))) (Nat.lor (Nat.shiftRight ne_15 (nat_lit 11)) (Nat.shiftLeft ne_15 (nat_lit 21)))) (Nat.lor (Nat.shiftRight ne_15 (nat_lit 25)) (Nat.shiftLeft ne_15 (nat_lit 7)))) (Nat.add (Nat.xor (Nat.land ne_15 ne_14) (Nat.land (Nat.xor ne_15 (nat_lit 4294967295)) ne_13)) (Nat.add (nat_lit 3835390401) w_16))))
  let na_16 := (Nat.land (Nat.add t1_16 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight na_15 (nat_lit 2)) (Nat.shiftLeft na_15 (nat_lit 30))) (Nat.lor (Nat.shiftRight na_15 (nat_lit 13)) (Nat.shiftLeft na_15 (nat_lit 19)))) (Nat.lor (Nat.shiftRight na_15 (nat_lit 22)) (Nat.shiftLeft na_15 (nat_lit 10)))) (Nat.xor (Nat.land na_15 (Nat.xor na_14 na_13)) (Nat.land na_14 na_13)))) (nat_lit 4294967295))
  let ne_16 := (Nat.land (Nat.add na_12 t1_16) (nat_lit 4294967295))
  let w_17 := (Nat.land (Nat.add (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight (nat_lit 256) (nat_lit 17)) (Nat.shiftLeft (nat_lit 256) (nat_lit 15))) (Nat.lor (Nat.shiftRight (nat_lit 256) (nat_lit 19)) (Nat.shiftLeft (nat_lit 256) (nat_lit 13)))) (Nat.shiftRight (nat_lit 256) (nat_lit 10))) (nat_lit 0)) (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight w_2 (nat_lit 7)) (Nat.shiftLeft w_2 (nat_lit 25))) (Nat.lor (Nat.shiftRight w_2 (nat_lit 18)) (Nat.shiftLeft w_2 (nat_lit 14)))) (Nat.shiftRight w_2 (nat_lit 3))) w_1)) (nat_lit 4294967295))
  let t1_17 := (Nat.add ne_13 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight ne_16 (nat_lit 6)) (Nat.shiftLeft ne_16 (nat_lit 26))) (Nat.lor (Nat.shiftRight ne_16 (nat_lit 11)) (Nat.shiftLeft ne_16 (nat_lit 21)))) (Nat.lor (Nat.shiftRight ne_16 (nat_lit 25)) (Nat.shiftLeft ne_16 (nat_lit 7)))) (Nat.add (Nat.xor (Nat.land ne_16 ne_15) (Nat.land (Nat.xor ne_16 (nat_lit 4294967295)) ne_14)) (Nat.add (nat_lit 4022224774) w_17))))
  let na_17 := (Nat.land (Nat.add t1_17 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight na_16 (nat_lit 2)) (Nat.shiftLeft na_16 (nat_lit 30))) (Nat.lor (Nat.shiftRight na_16 (nat_lit 13)) (Nat.shiftLeft na_16 (nat_lit 19)))) (Nat.lor (Nat.shiftRight na_16 (nat_lit 22)) (Nat.shiftLeft na_16 (nat_lit 10)))) (Nat.xor (Nat.land na_16 (Nat.xor na_15 na_14)) (Nat.land na_15 na_14)))) (nat_lit 4294967295))
  let ne_17 := (Nat.land (Nat.add na_13 t1_17) (nat_lit 4294967295))
  let w_18 := (Nat.land (Nat.add (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight w_16 (nat_lit 17)) (Nat.shiftLeft w_16 (nat_lit 15))) (Nat.lor (Nat.shiftRight w_16 (nat_lit 19)) (Nat.shiftLeft w_16 (nat_lit 13)))) (Nat.shiftRight w_16 (nat_lit 10))) (nat_lit 0)) (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight w_3 (nat_lit 7)) (Nat.shiftLeft w_3 (nat_lit 25))) (Nat.lor (Nat.shiftRight w_3 (nat_lit 18)) (Nat.shiftLeft w_3 (nat_lit 14)))) (Nat.shiftRight w_3 (nat_lit 3))) w_2)) (nat_lit 4294967295))
  let t1_18 := (Nat.add ne_14 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight ne_17 (nat_lit 6)) (Nat.shiftLeft ne_17 (nat_lit 26))) (Nat.lor (Nat.shiftRight ne_17 (nat_lit 11)) (Nat.shiftLeft ne_17 (nat_lit 21)))) (Nat.lor (Nat.shiftRight ne_17 (nat_lit 25)) (Nat.shiftLeft ne_17 (nat_lit 7)))) (Nat.add (Nat.xor (Nat.land ne_17 ne_16) (Nat.land (Nat.xor ne_17 (nat_lit 4294967295)) ne_15)) (Nat.add (nat_lit 264347078) w_18))))
  let na_18 := (Nat.land (Nat.add t1_18 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight na_17 (nat_lit 2)) (Nat.shiftLeft na_17 (nat_lit 30))) (Nat.lor (Nat.shiftRight na_17 (nat_lit 13)) (Nat.shiftLeft na_17 (nat_lit 19)))) (Nat.lor (Nat.shiftRight na_17 (nat_lit 22)) (Nat.shiftLeft na_17 (nat_lit 10)))) (Nat.xor (Nat.land na_17 (Nat.xor na_16 na_15)) (Nat.land na_16 na_15)))) (nat_lit 4294967295))
  let ne_18 := (Nat.land (Nat.add na_14 t1_18) (nat_lit 4294967295))
  let w_19 := (Nat.land (Nat.add (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight w_17 (nat_lit 17)) (Nat.shiftLeft w_17 (nat_lit 15))) (Nat.lor (Nat.shiftRight w_17 (nat_lit 19)) (Nat.shiftLeft w_17 (nat_lit 13)))) (Nat.shiftRight w_17 (nat_lit 10))) (nat_lit 0)) (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight w_4 (nat_lit 7)) (Nat.shiftLeft w_4 (nat_lit 25))) (Nat.lor (Nat.shiftRight w_4 (nat_lit 18)) (Nat.shiftLeft w_4 (nat_lit 14)))) (Nat.shiftRight w_4 (nat_lit 3))) w_3)) (nat_lit 4294967295))
  let t1_19 := (Nat.add ne_15 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight ne_18 (nat_lit 6)) (Nat.shiftLeft ne_18 (nat_lit 26))) (Nat.lor (Nat.shiftRight ne_18 (nat_lit 11)) (Nat.shiftLeft ne_18 (nat_lit 21)))) (Nat.lor (Nat.shiftRight ne_18 (nat_lit 25)) (Nat.shiftLeft ne_18 (nat_lit 7)))) (Nat.add (Nat.xor (Nat.land ne_18 ne_17) (Nat.land (Nat.xor ne_18 (nat_lit 4294967295)) ne_16)) (Nat.add (nat_lit 604807628) w_19))))
  let na_19 := (Nat.land (Nat.add t1_19 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight na_18 (nat_lit 2)) (Nat.shiftLeft na_18 (nat_lit 30))) (Nat.lor (Nat.shiftRight na_18 (nat_lit 13)) (Nat.shiftLeft na_18 (nat_lit 19)))) (Nat.lor (Nat.shiftRight na_18 (nat_lit 22)) (Nat.shiftLeft na_18 (nat_lit 10)))) (Nat.xor (Nat.land na_18 (Nat.xor na_17 na_16)) (Nat.land na_17 na_16)))) (nat_lit 4294967295))
  let ne_19 := (Nat.land (Nat.add na_15 t1_19) (nat_lit 4294967295))
  let w_20 := (Nat.land (Nat.add (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight w_18 (nat_lit 17)) (Nat.shiftLeft w_18 (nat_lit 15))) (Nat.lor (Nat.shiftRight w_18 (nat_lit 19)) (Nat.shiftLeft w_18 (nat_lit 13)))) (Nat.shiftRight w_18 (nat_lit 10))) (nat_lit 0)) (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight w_5 (nat_lit 7)) (Nat.shiftLeft w_5 (nat_lit 25))) (Nat.lor (Nat.shiftRight w_5 (nat_lit 18)) (Nat.shiftLeft w_5 (nat_lit 14)))) (Nat.shiftRight w_5 (nat_lit 3))) w_4)) (nat_lit 4294967295))
  let t1_20 := (Nat.add ne_16 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight ne_19 (nat_lit 6)) (Nat.shiftLeft ne_19 (nat_lit 26))) (Nat.lor (Nat.shiftRight ne_19 (nat_lit 11)) (Nat.shiftLeft ne_19 (nat_lit 21)))) (Nat.lor (Nat.shiftRight ne_19 (nat_lit 25)) (Nat.shiftLeft ne_19 (nat_lit 7)))) (Nat.add (Nat.xor (Nat.land ne_19 ne_18) (Nat.land (Nat.xor ne_19 (nat_lit 4294967295)) ne_17)) (Nat.add (nat_lit 770255983) w_20))))
  let na_20 := (Nat.land (Nat.add t1_20 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight na_19 (nat_lit 2)) (Nat.shiftLeft na_19 (nat_lit 30))) (Nat.lor (Nat.shiftRight na_19 (nat_lit 13)) (Nat.shiftLeft na_19 (nat_lit 19)))) (Nat.lor (Nat.shiftRight na_19 (nat_lit 22)) (Nat.shiftLeft na_19 (nat_lit 10)))) (Nat.xor (Nat.land na_19 (Nat.xor na_18 na_17)) (Nat.land na_18 na_17)))) (nat_lit 4294967295))
  let ne_20 := (Nat.land (Nat.add na_16 t1_20) (nat_lit 4294967295))
  let w_21 := (Nat.land (Nat.add (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight w_19 (nat_lit 17)) (Nat.shiftLeft w_19 (nat_lit 15))) (Nat.lor (Nat.shiftRight w_19 (nat_lit 19)) (Nat.shiftLeft w_19 (nat_lit 13)))) (Nat.shiftRight w_19 (nat_lit 10))) (nat_lit 0)) (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight w_6 (nat_lit 7)) (Nat.shiftLeft w_6 (nat_lit 25))) (Nat.lor (Nat.shiftRight w_6 (nat_lit 18)) (Nat.shiftLeft w_6 (nat_lit 14)))) (Nat.shiftRight w_6 (nat_lit 3))) w_5)) (nat_lit 4294967295))
  let t1_21 := (Nat.add ne_17 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight ne_20 (nat_lit 6)) (Nat.shiftLeft ne_20 (nat_lit 26))) (Nat.lor (Nat.shiftRight ne_20 (nat_lit 11)) (Nat.shiftLeft ne_20 (nat_lit 21)))) (Nat.lor (Nat.shiftRight ne_20 (nat_lit 25)) (Nat.shiftLeft ne_20 (nat_lit 7)))) (Nat.add (Nat.xor (Nat.land ne_20 ne_19) (Nat.land (Nat.xor ne_20 (nat_lit 4294967295)) ne_18)) (Nat.add (nat_lit 1249150122) w_21))))
  let na_21 := (Nat.land (Nat.add t1_21 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight na_20 (nat_lit 2)) (Nat.shiftLeft na_20 (nat_lit 30))) (Nat.lor (Nat.shiftRight na_20 (nat_lit 13)) (Nat.shiftLeft na_20 (nat_lit 19)))) (Nat.lor (Nat.shiftRight na_20 (nat_lit 22)) (Nat.shiftLeft na_20 (nat_lit 10)))) (Nat.xor (Nat.land na_20 (Nat.xor na_19 na_18)) (Nat.land na_19 na_18)))) (nat_lit 4294967295))
  let ne_21 := (Nat.land (Nat.add na_17 t1_21) (nat_lit 4294967295))
  let w_22 := (Nat.land (Nat.add (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight w_20 (nat_lit 17)) (Nat.shiftLeft w_20 (nat_lit 15))) (Nat.lor (Nat.shiftRight w_20 (nat_lit 19)) (Nat.shiftLeft w_20 (nat_lit 13)))) (Nat.shiftRight w_20 (nat_lit 10))) (nat_lit 256)) (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight w_7 (nat_lit 7)) (Nat.shiftLeft w_7 (nat_lit 25))) (Nat.lor (Nat.shiftRight w_7 (nat_lit 18)) (Nat.shiftLeft w_7 (nat_lit 14)))) (Nat.shiftRight w_7 (nat_lit 3))) w_6)) (nat_lit 4294967295))
  let t1_22 := (Nat.add ne_18 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight ne_21 (nat_lit 6)) (Nat.shiftLeft ne_21 (nat_lit 26))) (Nat.lor (Nat.shiftRight ne_21 (nat_lit 11)) (Nat.shiftLeft ne_21 (nat_lit 21)))) (Nat.lor (Nat.shiftRight ne_21 (nat_lit 25)) (Nat.shiftLeft ne_21 (nat_lit 7)))) (Nat.add (Nat.xor (Nat.land ne_21 ne_20) (Nat.land (Nat.xor ne_21 (nat_lit 4294967295)) ne_19)) (Nat.add (nat_lit 1555081692) w_22))))
  let na_22 := (Nat.land (Nat.add t1_22 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight na_21 (nat_lit 2)) (Nat.shiftLeft na_21 (nat_lit 30))) (Nat.lor (Nat.shiftRight na_21 (nat_lit 13)) (Nat.shiftLeft na_21 (nat_lit 19)))) (Nat.lor (Nat.shiftRight na_21 (nat_lit 22)) (Nat.shiftLeft na_21 (nat_lit 10)))) (Nat.xor (Nat.land na_21 (Nat.xor na_20 na_19)) (Nat.land na_20 na_19)))) (nat_lit 4294967295))
  let ne_22 := (Nat.land (Nat.add na_18 t1_22) (nat_lit 4294967295))
  let w_23 := (Nat.land (Nat.add (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight w_21 (nat_lit 17)) (Nat.shiftLeft w_21 (nat_lit 15))) (Nat.lor (Nat.shiftRight w_21 (nat_lit 19)) (Nat.shiftLeft w_21 (nat_lit 13)))) (Nat.shiftRight w_21 (nat_lit 10))) w_16) (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight (nat_lit 0x80000000) (nat_lit 7)) (Nat.shiftLeft (nat_lit 0x80000000) (nat_lit 25))) (Nat.lor (Nat.shiftRight (nat_lit 0x80000000) (nat_lit 18)) (Nat.shiftLeft (nat_lit 0x80000000) (nat_lit 14)))) (Nat.shiftRight (nat_lit 0x80000000) (nat_lit 3))) w_7)) (nat_lit 4294967295))
  let t1_23 := (Nat.add ne_19 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight ne_22 (nat_lit 6)) (Nat.shiftLeft ne_22 (nat_lit 26))) (Nat.lor (Nat.shiftRight ne_22 (nat_lit 11)) (Nat.shiftLeft ne_22 (nat_lit 21)))) (Nat.lor (Nat.shiftRight ne_22 (nat_lit 25)) (Nat.shiftLeft ne_22 (nat_lit 7)))) (Nat.add (Nat.xor (Nat.land ne_22 ne_21) (Nat.land (Nat.xor ne_22 (nat_lit 4294967295)) ne_20)) (Nat.add (nat_lit 1996064986) w_23))))
  let na_23 := (Nat.land (Nat.add t1_23 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight na_22 (nat_lit 2)) (Nat.shiftLeft na_22 (nat_lit 30))) (Nat.lor (Nat.shiftRight na_22 (nat_lit 13)) (Nat.shiftLeft na_22 (nat_lit 19)))) (Nat.lor (Nat.shiftRight na_22 (nat_lit 22)) (Nat.shiftLeft na_22 (nat_lit 10)))) (Nat.xor (Nat.land na_22 (Nat.xor na_21 na_20)) (Nat.land na_21 na_20)))) (nat_lit 4294967295))
  let ne_23 := (Nat.land (Nat.add na_19 t1_23) (nat_lit 4294967295))
  let w_24 := (Nat.land (Nat.add (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight w_22 (nat_lit 17)) (Nat.shiftLeft w_22 (nat_lit 15))) (Nat.lor (Nat.shiftRight w_22 (nat_lit 19)) (Nat.shiftLeft w_22 (nat_lit 13)))) (Nat.shiftRight w_22 (nat_lit 10))) w_17) (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight (nat_lit 0) (nat_lit 7)) (Nat.shiftLeft (nat_lit 0) (nat_lit 25))) (Nat.lor (Nat.shiftRight (nat_lit 0) (nat_lit 18)) (Nat.shiftLeft (nat_lit 0) (nat_lit 14)))) (Nat.shiftRight (nat_lit 0) (nat_lit 3))) (nat_lit 0x80000000))) (nat_lit 4294967295))
  let t1_24 := (Nat.add ne_20 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight ne_23 (nat_lit 6)) (Nat.shiftLeft ne_23 (nat_lit 26))) (Nat.lor (Nat.shiftRight ne_23 (nat_lit 11)) (Nat.shiftLeft ne_23 (nat_lit 21)))) (Nat.lor (Nat.shiftRight ne_23 (nat_lit 25)) (Nat.shiftLeft ne_23 (nat_lit 7)))) (Nat.add (Nat.xor (Nat.land ne_23 ne_22) (Nat.land (Nat.xor ne_23 (nat_lit 4294967295)) ne_21)) (Nat.add (nat_lit 2554220882) w_24))))
  let na_24 := (Nat.land (Nat.add t1_24 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight na_23 (nat_lit 2)) (Nat.shiftLeft na_23 (nat_lit 30))) (Nat.lor (Nat.shiftRight na_23 (nat_lit 13)) (Nat.shiftLeft na_23 (nat_lit 19)))) (Nat.lor (Nat.shiftRight na_23 (nat_lit 22)) (Nat.shiftLeft na_23 (nat_lit 10)))) (Nat.xor (Nat.land na_23 (Nat.xor na_22 na_21)) (Nat.land na_22 na_21)))) (nat_lit 4294967295))
  let ne_24 := (Nat.land (Nat.add na_20 t1_24) (nat_lit 4294967295))
  let w_25 := (Nat.land (Nat.add (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight w_23 (nat_lit 17)) (Nat.shiftLeft w_23 (nat_lit 15))) (Nat.lor (Nat.shiftRight w_23 (nat_lit 19)) (Nat.shiftLeft w_23 (nat_lit 13)))) (Nat.shiftRight w_23 (nat_lit 10))) w_18) (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight (nat_lit 0) (nat_lit 7)) (Nat.shiftLeft (nat_lit 0) (nat_lit 25))) (Nat.lor (Nat.shiftRight (nat_lit 0) (nat_lit 18)) (Nat.shiftLeft (nat_lit 0) (nat_lit 14)))) (Nat.shiftRight (nat_lit 0) (nat_lit 3))) (nat_lit 0))) (nat_lit 4294967295))
  let t1_25 := (Nat.add ne_21 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight ne_24 (nat_lit 6)) (Nat.shiftLeft ne_24 (nat_lit 26))) (Nat.lor (Nat.shiftRight ne_24 (nat_lit 11)) (Nat.shiftLeft ne_24 (nat_lit 21)))) (Nat.lor (Nat.shiftRight ne_24 (nat_lit 25)) (Nat.shiftLeft ne_24 (nat_lit 7)))) (Nat.add (Nat.xor (Nat.land ne_24 ne_23) (Nat.land (Nat.xor ne_24 (nat_lit 4294967295)) ne_22)) (Nat.add (nat_lit 2821834349) w_25))))
  let na_25 := (Nat.land (Nat.add t1_25 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight na_24 (nat_lit 2)) (Nat.shiftLeft na_24 (nat_lit 30))) (Nat.lor (Nat.shiftRight na_24 (nat_lit 13)) (Nat.shiftLeft na_24 (nat_lit 19)))) (Nat.lor (Nat.shiftRight na_24 (nat_lit 22)) (Nat.shiftLeft na_24 (nat_lit 10)))) (Nat.xor (Nat.land na_24 (Nat.xor na_23 na_22)) (Nat.land na_23 na_22)))) (nat_lit 4294967295))
  let ne_25 := (Nat.land (Nat.add na_21 t1_25) (nat_lit 4294967295))
  let w_26 := (Nat.land (Nat.add (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight w_24 (nat_lit 17)) (Nat.shiftLeft w_24 (nat_lit 15))) (Nat.lor (Nat.shiftRight w_24 (nat_lit 19)) (Nat.shiftLeft w_24 (nat_lit 13)))) (Nat.shiftRight w_24 (nat_lit 10))) w_19) (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight (nat_lit 0) (nat_lit 7)) (Nat.shiftLeft (nat_lit 0) (nat_lit 25))) (Nat.lor (Nat.shiftRight (nat_lit 0) (nat_lit 18)) (Nat.shiftLeft (nat_lit 0) (nat_lit 14)))) (Nat.shiftRight (nat_lit 0) (nat_lit 3))) (nat_lit 0))) (nat_lit 4294967295))
  let t1_26 := (Nat.add ne_22 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight ne_25 (nat_lit 6)) (Nat.shiftLeft ne_25 (nat_lit 26))) (Nat.lor (Nat.shiftRight ne_25 (nat_lit 11)) (Nat.shiftLeft ne_25 (nat_lit 21)))) (Nat.lor (Nat.shiftRight ne_25 (nat_lit 25)) (Nat.shiftLeft ne_25 (nat_lit 7)))) (Nat.add (Nat.xor (Nat.land ne_25 ne_24) (Nat.land (Nat.xor ne_25 (nat_lit 4294967295)) ne_23)) (Nat.add (nat_lit 2952996808) w_26))))
  let na_26 := (Nat.land (Nat.add t1_26 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight na_25 (nat_lit 2)) (Nat.shiftLeft na_25 (nat_lit 30))) (Nat.lor (Nat.shiftRight na_25 (nat_lit 13)) (Nat.shiftLeft na_25 (nat_lit 19)))) (Nat.lor (Nat.shiftRight na_25 (nat_lit 22)) (Nat.shiftLeft na_25 (nat_lit 10)))) (Nat.xor (Nat.land na_25 (Nat.xor na_24 na_23)) (Nat.land na_24 na_23)))) (nat_lit 4294967295))
  let ne_26 := (Nat.land (Nat.add na_22 t1_26) (nat_lit 4294967295))
  let w_27 := (Nat.land (Nat.add (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight w_25 (nat_lit 17)) (Nat.shiftLeft w_25 (nat_lit 15))) (Nat.lor (Nat.shiftRight w_25 (nat_lit 19)) (Nat.shiftLeft w_25 (nat_lit 13)))) (Nat.shiftRight w_25 (nat_lit 10))) w_20) (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight (nat_lit 0) (nat_lit 7)) (Nat.shiftLeft (nat_lit 0) (nat_lit 25))) (Nat.lor (Nat.shiftRight (nat_lit 0) (nat_lit 18)) (Nat.shiftLeft (nat_lit 0) (nat_lit 14)))) (Nat.shiftRight (nat_lit 0) (nat_lit 3))) (nat_lit 0))) (nat_lit 4294967295))
  let t1_27 := (Nat.add ne_23 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight ne_26 (nat_lit 6)) (Nat.shiftLeft ne_26 (nat_lit 26))) (Nat.lor (Nat.shiftRight ne_26 (nat_lit 11)) (Nat.shiftLeft ne_26 (nat_lit 21)))) (Nat.lor (Nat.shiftRight ne_26 (nat_lit 25)) (Nat.shiftLeft ne_26 (nat_lit 7)))) (Nat.add (Nat.xor (Nat.land ne_26 ne_25) (Nat.land (Nat.xor ne_26 (nat_lit 4294967295)) ne_24)) (Nat.add (nat_lit 3210313671) w_27))))
  let na_27 := (Nat.land (Nat.add t1_27 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight na_26 (nat_lit 2)) (Nat.shiftLeft na_26 (nat_lit 30))) (Nat.lor (Nat.shiftRight na_26 (nat_lit 13)) (Nat.shiftLeft na_26 (nat_lit 19)))) (Nat.lor (Nat.shiftRight na_26 (nat_lit 22)) (Nat.shiftLeft na_26 (nat_lit 10)))) (Nat.xor (Nat.land na_26 (Nat.xor na_25 na_24)) (Nat.land na_25 na_24)))) (nat_lit 4294967295))
  let ne_27 := (Nat.land (Nat.add na_23 t1_27) (nat_lit 4294967295))
  let w_28 := (Nat.land (Nat.add (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight w_26 (nat_lit 17)) (Nat.shiftLeft w_26 (nat_lit 15))) (Nat.lor (Nat.shiftRight w_26 (nat_lit 19)) (Nat.shiftLeft w_26 (nat_lit 13)))) (Nat.shiftRight w_26 (nat_lit 10))) w_21) (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight (nat_lit 0) (nat_lit 7)) (Nat.shiftLeft (nat_lit 0) (nat_lit 25))) (Nat.lor (Nat.shiftRight (nat_lit 0) (nat_lit 18)) (Nat.shiftLeft (nat_lit 0) (nat_lit 14)))) (Nat.shiftRight (nat_lit 0) (nat_lit 3))) (nat_lit 0))) (nat_lit 4294967295))
  let t1_28 := (Nat.add ne_24 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight ne_27 (nat_lit 6)) (Nat.shiftLeft ne_27 (nat_lit 26))) (Nat.lor (Nat.shiftRight ne_27 (nat_lit 11)) (Nat.shiftLeft ne_27 (nat_lit 21)))) (Nat.lor (Nat.shiftRight ne_27 (nat_lit 25)) (Nat.shiftLeft ne_27 (nat_lit 7)))) (Nat.add (Nat.xor (Nat.land ne_27 ne_26) (Nat.land (Nat.xor ne_27 (nat_lit 4294967295)) ne_25)) (Nat.add (nat_lit 3336571891) w_28))))
  let na_28 := (Nat.land (Nat.add t1_28 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight na_27 (nat_lit 2)) (Nat.shiftLeft na_27 (nat_lit 30))) (Nat.lor (Nat.shiftRight na_27 (nat_lit 13)) (Nat.shiftLeft na_27 (nat_lit 19)))) (Nat.lor (Nat.shiftRight na_27 (nat_lit 22)) (Nat.shiftLeft na_27 (nat_lit 10)))) (Nat.xor (Nat.land na_27 (Nat.xor na_26 na_25)) (Nat.land na_26 na_25)))) (nat_lit 4294967295))
  let ne_28 := (Nat.land (Nat.add na_24 t1_28) (nat_lit 4294967295))
  let w_29 := (Nat.land (Nat.add (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight w_27 (nat_lit 17)) (Nat.shiftLeft w_27 (nat_lit 15))) (Nat.lor (Nat.shiftRight w_27 (nat_lit 19)) (Nat.shiftLeft w_27 (nat_lit 13)))) (Nat.shiftRight w_27 (nat_lit 10))) w_22) (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight (nat_lit 0) (nat_lit 7)) (Nat.shiftLeft (nat_lit 0) (nat_lit 25))) (Nat.lor (Nat.shiftRight (nat_lit 0) (nat_lit 18)) (Nat.shiftLeft (nat_lit 0) (nat_lit 14)))) (Nat.shiftRight (nat_lit 0) (nat_lit 3))) (nat_lit 0))) (nat_lit 4294967295))
  let t1_29 := (Nat.add ne_25 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight ne_28 (nat_lit 6)) (Nat.shiftLeft ne_28 (nat_lit 26))) (Nat.lor (Nat.shiftRight ne_28 (nat_lit 11)) (Nat.shiftLeft ne_28 (nat_lit 21)))) (Nat.lor (Nat.shiftRight ne_28 (nat_lit 25)) (Nat.shiftLeft ne_28 (nat_lit 7)))) (Nat.add (Nat.xor (Nat.land ne_28 ne_27) (Nat.land (Nat.xor ne_28 (nat_lit 4294967295)) ne_26)) (Nat.add (nat_lit 3584528711) w_29))))
  let na_29 := (Nat.land (Nat.add t1_29 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight na_28 (nat_lit 2)) (Nat.shiftLeft na_28 (nat_lit 30))) (Nat.lor (Nat.shiftRight na_28 (nat_lit 13)) (Nat.shiftLeft na_28 (nat_lit 19)))) (Nat.lor (Nat.shiftRight na_28 (nat_lit 22)) (Nat.shiftLeft na_28 (nat_lit 10)))) (Nat.xor (Nat.land na_28 (Nat.xor na_27 na_26)) (Nat.land na_27 na_26)))) (nat_lit 4294967295))
  let ne_29 := (Nat.land (Nat.add na_25 t1_29) (nat_lit 4294967295))
  let w_30 := (Nat.land (Nat.add (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight w_28 (nat_lit 17)) (Nat.shiftLeft w_28 (nat_lit 15))) (Nat.lor (Nat.shiftRight w_28 (nat_lit 19)) (Nat.shiftLeft w_28 (nat_lit 13)))) (Nat.shiftRight w_28 (nat_lit 10))) w_23) (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight (nat_lit 256) (nat_lit 7)) (Nat.shiftLeft (nat_lit 256) (nat_lit 25))) (Nat.lor (Nat.shiftRight (nat_lit 256) (nat_lit 18)) (Nat.shiftLeft (nat_lit 256) (nat_lit 14)))) (Nat.shiftRight (nat_lit 256) (nat_lit 3))) (nat_lit 0))) (nat_lit 4294967295))
  let t1_30 := (Nat.add ne_26 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight ne_29 (nat_lit 6)) (Nat.shiftLeft ne_29 (nat_lit 26))) (Nat.lor (Nat.shiftRight ne_29 (nat_lit 11)) (Nat.shiftLeft ne_29 (nat_lit 21)))) (Nat.lor (Nat.shiftRight ne_29 (nat_lit 25)) (Nat.shiftLeft ne_29 (nat_lit 7)))) (Nat.add (Nat.xor (Nat.land ne_29 ne_28) (Nat.land (Nat.xor ne_29 (nat_lit 4294967295)) ne_27)) (Nat.add (nat_lit 113926993) w_30))))
  let na_30 := (Nat.land (Nat.add t1_30 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight na_29 (nat_lit 2)) (Nat.shiftLeft na_29 (nat_lit 30))) (Nat.lor (Nat.shiftRight na_29 (nat_lit 13)) (Nat.shiftLeft na_29 (nat_lit 19)))) (Nat.lor (Nat.shiftRight na_29 (nat_lit 22)) (Nat.shiftLeft na_29 (nat_lit 10)))) (Nat.xor (Nat.land na_29 (Nat.xor na_28 na_27)) (Nat.land na_28 na_27)))) (nat_lit 4294967295))
  let ne_30 := (Nat.land (Nat.add na_26 t1_30) (nat_lit 4294967295))
  let w_31 := (Nat.land (Nat.add (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight w_29 (nat_lit 17)) (Nat.shiftLeft w_29 (nat_lit 15))) (Nat.lor (Nat.shiftRight w_29 (nat_lit 19)) (Nat.shiftLeft w_29 (nat_lit 13)))) (Nat.shiftRight w_29 (nat_lit 10))) w_24) (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight w_16 (nat_lit 7)) (Nat.shiftLeft w_16 (nat_lit 25))) (Nat.lor (Nat.shiftRight w_16 (nat_lit 18)) (Nat.shiftLeft w_16 (nat_lit 14)))) (Nat.shiftRight w_16 (nat_lit 3))) (nat_lit 256))) (nat_lit 4294967295))
  let t1_31 := (Nat.add ne_27 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight ne_30 (nat_lit 6)) (Nat.shiftLeft ne_30 (nat_lit 26))) (Nat.lor (Nat.shiftRight ne_30 (nat_lit 11)) (Nat.shiftLeft ne_30 (nat_lit 21)))) (Nat.lor (Nat.shiftRight ne_30 (nat_lit 25)) (Nat.shiftLeft ne_30 (nat_lit 7)))) (Nat.add (Nat.xor (Nat.land ne_30 ne_29) (Nat.land (Nat.xor ne_30 (nat_lit 4294967295)) ne_28)) (Nat.add (nat_lit 338241895) w_31))))
  let na_31 := (Nat.land (Nat.add t1_31 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight na_30 (nat_lit 2)) (Nat.shiftLeft na_30 (nat_lit 30))) (Nat.lor (Nat.shiftRight na_30 (nat_lit 13)) (Nat.shiftLeft na_30 (nat_lit 19)))) (Nat.lor (Nat.shiftRight na_30 (nat_lit 22)) (Nat.shiftLeft na_30 (nat_lit 10)))) (Nat.xor (Nat.land na_30 (Nat.xor na_29 na_28)) (Nat.land na_29 na_28)))) (nat_lit 4294967295))
  let ne_31 := (Nat.land (Nat.add na_27 t1_31) (nat_lit 4294967295))
  let w_32 := (Nat.land (Nat.add (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight w_30 (nat_lit 17)) (Nat.shiftLeft w_30 (nat_lit 15))) (Nat.lor (Nat.shiftRight w_30 (nat_lit 19)) (Nat.shiftLeft w_30 (nat_lit 13)))) (Nat.shiftRight w_30 (nat_lit 10))) w_25) (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight w_17 (nat_lit 7)) (Nat.shiftLeft w_17 (nat_lit 25))) (Nat.lor (Nat.shiftRight w_17 (nat_lit 18)) (Nat.shiftLeft w_17 (nat_lit 14)))) (Nat.shiftRight w_17 (nat_lit 3))) w_16)) (nat_lit 4294967295))
  let t1_32 := (Nat.add ne_28 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight ne_31 (nat_lit 6)) (Nat.shiftLeft ne_31 (nat_lit 26))) (Nat.lor (Nat.shiftRight ne_31 (nat_lit 11)) (Nat.shiftLeft ne_31 (nat_lit 21)))) (Nat.lor (Nat.shiftRight ne_31 (nat_lit 25)) (Nat.shiftLeft ne_31 (nat_lit 7)))) (Nat.add (Nat.xor (Nat.land ne_31 ne_30) (Nat.land (Nat.xor ne_31 (nat_lit 4294967295)) ne_29)) (Nat.add (nat_lit 666307205) w_32))))
  let na_32 := (Nat.land (Nat.add t1_32 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight na_31 (nat_lit 2)) (Nat.shiftLeft na_31 (nat_lit 30))) (Nat.lor (Nat.shiftRight na_31 (nat_lit 13)) (Nat.shiftLeft na_31 (nat_lit 19)))) (Nat.lor (Nat.shiftRight na_31 (nat_lit 22)) (Nat.shiftLeft na_31 (nat_lit 10)))) (Nat.xor (Nat.land na_31 (Nat.xor na_30 na_29)) (Nat.land na_30 na_29)))) (nat_lit 4294967295))
  let ne_32 := (Nat.land (Nat.add na_28 t1_32) (nat_lit 4294967295))
  let w_33 := (Nat.land (Nat.add (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight w_31 (nat_lit 17)) (Nat.shiftLeft w_31 (nat_lit 15))) (Nat.lor (Nat.shiftRight w_31 (nat_lit 19)) (Nat.shiftLeft w_31 (nat_lit 13)))) (Nat.shiftRight w_31 (nat_lit 10))) w_26) (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight w_18 (nat_lit 7)) (Nat.shiftLeft w_18 (nat_lit 25))) (Nat.lor (Nat.shiftRight w_18 (nat_lit 18)) (Nat.shiftLeft w_18 (nat_lit 14)))) (Nat.shiftRight w_18 (nat_lit 3))) w_17)) (nat_lit 4294967295))
  let t1_33 := (Nat.add ne_29 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight ne_32 (nat_lit 6)) (Nat.shiftLeft ne_32 (nat_lit 26))) (Nat.lor (Nat.shiftRight ne_32 (nat_lit 11)) (Nat.shiftLeft ne_32 (nat_lit 21)))) (Nat.lor (Nat.shiftRight ne_32 (nat_lit 25)) (Nat.shiftLeft ne_32 (nat_lit 7)))) (Nat.add (Nat.xor (Nat.land ne_32 ne_31) (Nat.land (Nat.xor ne_32 (nat_lit 4294967295)) ne_30)) (Nat.add (nat_lit 773529912) w_33))))
  let na_33 := (Nat.land (Nat.add t1_33 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight na_32 (nat_lit 2)) (Nat.shiftLeft na_32 (nat_lit 30))) (Nat.lor (Nat.shiftRight na_32 (nat_lit 13)) (Nat.shiftLeft na_32 (nat_lit 19)))) (Nat.lor (Nat.shiftRight na_32 (nat_lit 22)) (Nat.shiftLeft na_32 (nat_lit 10)))) (Nat.xor (Nat.land na_32 (Nat.xor na_31 na_30)) (Nat.land na_31 na_30)))) (nat_lit 4294967295))
  let ne_33 := (Nat.land (Nat.add na_29 t1_33) (nat_lit 4294967295))
  let w_34 := (Nat.land (Nat.add (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight w_32 (nat_lit 17)) (Nat.shiftLeft w_32 (nat_lit 15))) (Nat.lor (Nat.shiftRight w_32 (nat_lit 19)) (Nat.shiftLeft w_32 (nat_lit 13)))) (Nat.shiftRight w_32 (nat_lit 10))) w_27) (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight w_19 (nat_lit 7)) (Nat.shiftLeft w_19 (nat_lit 25))) (Nat.lor (Nat.shiftRight w_19 (nat_lit 18)) (Nat.shiftLeft w_19 (nat_lit 14)))) (Nat.shiftRight w_19 (nat_lit 3))) w_18)) (nat_lit 4294967295))
  let t1_34 := (Nat.add ne_30 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight ne_33 (nat_lit 6)) (Nat.shiftLeft ne_33 (nat_lit 26))) (Nat.lor (Nat.shiftRight ne_33 (nat_lit 11)) (Nat.shiftLeft ne_33 (nat_lit 21)))) (Nat.lor (Nat.shiftRight ne_33 (nat_lit 25)) (Nat.shiftLeft ne_33 (nat_lit 7)))) (Nat.add (Nat.xor (Nat.land ne_33 ne_32) (Nat.land (Nat.xor ne_33 (nat_lit 4294967295)) ne_31)) (Nat.add (nat_lit 1294757372) w_34))))
  let na_34 := (Nat.land (Nat.add t1_34 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight na_33 (nat_lit 2)) (Nat.shiftLeft na_33 (nat_lit 30))) (Nat.lor (Nat.shiftRight na_33 (nat_lit 13)) (Nat.shiftLeft na_33 (nat_lit 19)))) (Nat.lor (Nat.shiftRight na_33 (nat_lit 22)) (Nat.shiftLeft na_33 (nat_lit 10)))) (Nat.xor (Nat.land na_33 (Nat.xor na_32 na_31)) (Nat.land na_32 na_31)))) (nat_lit 4294967295))
  let ne_34 := (Nat.land (Nat.add na_30 t1_34) (nat_lit 4294967295))
  let w_35 := (Nat.land (Nat.add (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight w_33 (nat_lit 17)) (Nat.shiftLeft w_33 (nat_lit 15))) (Nat.lor (Nat.shiftRight w_33 (nat_lit 19)) (Nat.shiftLeft w_33 (nat_lit 13)))) (Nat.shiftRight w_33 (nat_lit 10))) w_28) (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight w_20 (nat_lit 7)) (Nat.shiftLeft w_20 (nat_lit 25))) (Nat.lor (Nat.shiftRight w_20 (nat_lit 18)) (Nat.shiftLeft w_20 (nat_lit 14)))) (Nat.shiftRight w_20 (nat_lit 3))) w_19)) (nat_lit 4294967295))
  let t1_35 := (Nat.add ne_31 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight ne_34 (nat_lit 6)) (Nat.shiftLeft ne_34 (nat_lit 26))) (Nat.lor (Nat.shiftRight ne_34 (nat_lit 11)) (Nat.shiftLeft ne_34 (nat_lit 21)))) (Nat.lor (Nat.shiftRight ne_34 (nat_lit 25)) (Nat.shiftLeft ne_34 (nat_lit 7)))) (Nat.add (Nat.xor (Nat.land ne_34 ne_33) (Nat.land (Nat.xor ne_34 (nat_lit 4294967295)) ne_32)) (Nat.add (nat_lit 1396182291) w_35))))
  let na_35 := (Nat.land (Nat.add t1_35 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight na_34 (nat_lit 2)) (Nat.shiftLeft na_34 (nat_lit 30))) (Nat.lor (Nat.shiftRight na_34 (nat_lit 13)) (Nat.shiftLeft na_34 (nat_lit 19)))) (Nat.lor (Nat.shiftRight na_34 (nat_lit 22)) (Nat.shiftLeft na_34 (nat_lit 10)))) (Nat.xor (Nat.land na_34 (Nat.xor na_33 na_32)) (Nat.land na_33 na_32)))) (nat_lit 4294967295))
  let ne_35 := (Nat.land (Nat.add na_31 t1_35) (nat_lit 4294967295))
  let w_36 := (Nat.land (Nat.add (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight w_34 (nat_lit 17)) (Nat.shiftLeft w_34 (nat_lit 15))) (Nat.lor (Nat.shiftRight w_34 (nat_lit 19)) (Nat.shiftLeft w_34 (nat_lit 13)))) (Nat.shiftRight w_34 (nat_lit 10))) w_29) (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight w_21 (nat_lit 7)) (Nat.shiftLeft w_21 (nat_lit 25))) (Nat.lor (Nat.shiftRight w_21 (nat_lit 18)) (Nat.shiftLeft w_21 (nat_lit 14)))) (Nat.shiftRight w_21 (nat_lit 3))) w_20)) (nat_lit 4294967295))
  let t1_36 := (Nat.add ne_32 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight ne_35 (nat_lit 6)) (Nat.shiftLeft ne_35 (nat_lit 26))) (Nat.lor (Nat.shiftRight ne_35 (nat_lit 11)) (Nat.shiftLeft ne_35 (nat_lit 21)))) (Nat.lor (Nat.shiftRight ne_35 (nat_lit 25)) (Nat.shiftLeft ne_35 (nat_lit 7)))) (Nat.add (Nat.xor (Nat.land ne_35 ne_34) (Nat.land (Nat.xor ne_35 (nat_lit 4294967295)) ne_33)) (Nat.add (nat_lit 1695183700) w_36))))
  let na_36 := (Nat.land (Nat.add t1_36 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight na_35 (nat_lit 2)) (Nat.shiftLeft na_35 (nat_lit 30))) (Nat.lor (Nat.shiftRight na_35 (nat_lit 13)) (Nat.shiftLeft na_35 (nat_lit 19)))) (Nat.lor (Nat.shiftRight na_35 (nat_lit 22)) (Nat.shiftLeft na_35 (nat_lit 10)))) (Nat.xor (Nat.land na_35 (Nat.xor na_34 na_33)) (Nat.land na_34 na_33)))) (nat_lit 4294967295))
  let ne_36 := (Nat.land (Nat.add na_32 t1_36) (nat_lit 4294967295))
  let w_37 := (Nat.land (Nat.add (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight w_35 (nat_lit 17)) (Nat.shiftLeft w_35 (nat_lit 15))) (Nat.lor (Nat.shiftRight w_35 (nat_lit 19)) (Nat.shiftLeft w_35 (nat_lit 13)))) (Nat.shiftRight w_35 (nat_lit 10))) w_30) (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight w_22 (nat_lit 7)) (Nat.shiftLeft w_22 (nat_lit 25))) (Nat.lor (Nat.shiftRight w_22 (nat_lit 18)) (Nat.shiftLeft w_22 (nat_lit 14)))) (Nat.shiftRight w_22 (nat_lit 3))) w_21)) (nat_lit 4294967295))
  let t1_37 := (Nat.add ne_33 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight ne_36 (nat_lit 6)) (Nat.shiftLeft ne_36 (nat_lit 26))) (Nat.lor (Nat.shiftRight ne_36 (nat_lit 11)) (Nat.shiftLeft ne_36 (nat_lit 21)))) (Nat.lor (Nat.shiftRight ne_36 (nat_lit 25)) (Nat.shiftLeft ne_36 (nat_lit 7)))) (Nat.add (Nat.xor (Nat.land ne_36 ne_35) (Nat.land (Nat.xor ne_36 (nat_lit 4294967295)) ne_34)) (Nat.add (nat_lit 1986661051) w_37))))
  let na_37 := (Nat.land (Nat.add t1_37 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight na_36 (nat_lit 2)) (Nat.shiftLeft na_36 (nat_lit 30))) (Nat.lor (Nat.shiftRight na_36 (nat_lit 13)) (Nat.shiftLeft na_36 (nat_lit 19)))) (Nat.lor (Nat.shiftRight na_36 (nat_lit 22)) (Nat.shiftLeft na_36 (nat_lit 10)))) (Nat.xor (Nat.land na_36 (Nat.xor na_35 na_34)) (Nat.land na_35 na_34)))) (nat_lit 4294967295))
  let ne_37 := (Nat.land (Nat.add na_33 t1_37) (nat_lit 4294967295))
  let w_38 := (Nat.land (Nat.add (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight w_36 (nat_lit 17)) (Nat.shiftLeft w_36 (nat_lit 15))) (Nat.lor (Nat.shiftRight w_36 (nat_lit 19)) (Nat.shiftLeft w_36 (nat_lit 13)))) (Nat.shiftRight w_36 (nat_lit 10))) w_31) (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight w_23 (nat_lit 7)) (Nat.shiftLeft w_23 (nat_lit 25))) (Nat.lor (Nat.shiftRight w_23 (nat_lit 18)) (Nat.shiftLeft w_23 (nat_lit 14)))) (Nat.shiftRight w_23 (nat_lit 3))) w_22)) (nat_lit 4294967295))
  let t1_38 := (Nat.add ne_34 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight ne_37 (nat_lit 6)) (Nat.shiftLeft ne_37 (nat_lit 26))) (Nat.lor (Nat.shiftRight ne_37 (nat_lit 11)) (Nat.shiftLeft ne_37 (nat_lit 21)))) (Nat.lor (Nat.shiftRight ne_37 (nat_lit 25)) (Nat.shiftLeft ne_37 (nat_lit 7)))) (Nat.add (Nat.xor (Nat.land ne_37 ne_36) (Nat.land (Nat.xor ne_37 (nat_lit 4294967295)) ne_35)) (Nat.add (nat_lit 2177026350) w_38))))
  let na_38 := (Nat.land (Nat.add t1_38 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight na_37 (nat_lit 2)) (Nat.shiftLeft na_37 (nat_lit 30))) (Nat.lor (Nat.shiftRight na_37 (nat_lit 13)) (Nat.shiftLeft na_37 (nat_lit 19)))) (Nat.lor (Nat.shiftRight na_37 (nat_lit 22)) (Nat.shiftLeft na_37 (nat_lit 10)))) (Nat.xor (Nat.land na_37 (Nat.xor na_36 na_35)) (Nat.land na_36 na_35)))) (nat_lit 4294967295))
  let ne_38 := (Nat.land (Nat.add na_34 t1_38) (nat_lit 4294967295))
  let w_39 := (Nat.land (Nat.add (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight w_37 (nat_lit 17)) (Nat.shiftLeft w_37 (nat_lit 15))) (Nat.lor (Nat.shiftRight w_37 (nat_lit 19)) (Nat.shiftLeft w_37 (nat_lit 13)))) (Nat.shiftRight w_37 (nat_lit 10))) w_32) (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight w_24 (nat_lit 7)) (Nat.shiftLeft w_24 (nat_lit 25))) (Nat.lor (Nat.shiftRight w_24 (nat_lit 18)) (Nat.shiftLeft w_24 (nat_lit 14)))) (Nat.shiftRight w_24 (nat_lit 3))) w_23)) (nat_lit 4294967295))
  let t1_39 := (Nat.add ne_35 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight ne_38 (nat_lit 6)) (Nat.shiftLeft ne_38 (nat_lit 26))) (Nat.lor (Nat.shiftRight ne_38 (nat_lit 11)) (Nat.shiftLeft ne_38 (nat_lit 21)))) (Nat.lor (Nat.shiftRight ne_38 (nat_lit 25)) (Nat.shiftLeft ne_38 (nat_lit 7)))) (Nat.add (Nat.xor (Nat.land ne_38 ne_37) (Nat.land (Nat.xor ne_38 (nat_lit 4294967295)) ne_36)) (Nat.add (nat_lit 2456956037) w_39))))
  let na_39 := (Nat.land (Nat.add t1_39 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight na_38 (nat_lit 2)) (Nat.shiftLeft na_38 (nat_lit 30))) (Nat.lor (Nat.shiftRight na_38 (nat_lit 13)) (Nat.shiftLeft na_38 (nat_lit 19)))) (Nat.lor (Nat.shiftRight na_38 (nat_lit 22)) (Nat.shiftLeft na_38 (nat_lit 10)))) (Nat.xor (Nat.land na_38 (Nat.xor na_37 na_36)) (Nat.land na_37 na_36)))) (nat_lit 4294967295))
  let ne_39 := (Nat.land (Nat.add na_35 t1_39) (nat_lit 4294967295))
  let w_40 := (Nat.land (Nat.add (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight w_38 (nat_lit 17)) (Nat.shiftLeft w_38 (nat_lit 15))) (Nat.lor (Nat.shiftRight w_38 (nat_lit 19)) (Nat.shiftLeft w_38 (nat_lit 13)))) (Nat.shiftRight w_38 (nat_lit 10))) w_33) (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight w_25 (nat_lit 7)) (Nat.shiftLeft w_25 (nat_lit 25))) (Nat.lor (Nat.shiftRight w_25 (nat_lit 18)) (Nat.shiftLeft w_25 (nat_lit 14)))) (Nat.shiftRight w_25 (nat_lit 3))) w_24)) (nat_lit 4294967295))
  let t1_40 := (Nat.add ne_36 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight ne_39 (nat_lit 6)) (Nat.shiftLeft ne_39 (nat_lit 26))) (Nat.lor (Nat.shiftRight ne_39 (nat_lit 11)) (Nat.shiftLeft ne_39 (nat_lit 21)))) (Nat.lor (Nat.shiftRight ne_39 (nat_lit 25)) (Nat.shiftLeft ne_39 (nat_lit 7)))) (Nat.add (Nat.xor (Nat.land ne_39 ne_38) (Nat.land (Nat.xor ne_39 (nat_lit 4294967295)) ne_37)) (Nat.add (nat_lit 2730485921) w_40))))
  let na_40 := (Nat.land (Nat.add t1_40 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight na_39 (nat_lit 2)) (Nat.shiftLeft na_39 (nat_lit 30))) (Nat.lor (Nat.shiftRight na_39 (nat_lit 13)) (Nat.shiftLeft na_39 (nat_lit 19)))) (Nat.lor (Nat.shiftRight na_39 (nat_lit 22)) (Nat.shiftLeft na_39 (nat_lit 10)))) (Nat.xor (Nat.land na_39 (Nat.xor na_38 na_37)) (Nat.land na_38 na_37)))) (nat_lit 4294967295))
  let ne_40 := (Nat.land (Nat.add na_36 t1_40) (nat_lit 4294967295))
  let w_41 := (Nat.land (Nat.add (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight w_39 (nat_lit 17)) (Nat.shiftLeft w_39 (nat_lit 15))) (Nat.lor (Nat.shiftRight w_39 (nat_lit 19)) (Nat.shiftLeft w_39 (nat_lit 13)))) (Nat.shiftRight w_39 (nat_lit 10))) w_34) (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight w_26 (nat_lit 7)) (Nat.shiftLeft w_26 (nat_lit 25))) (Nat.lor (Nat.shiftRight w_26 (nat_lit 18)) (Nat.shiftLeft w_26 (nat_lit 14)))) (Nat.shiftRight w_26 (nat_lit 3))) w_25)) (nat_lit 4294967295))
  let t1_41 := (Nat.add ne_37 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight ne_40 (nat_lit 6)) (Nat.shiftLeft ne_40 (nat_lit 26))) (Nat.lor (Nat.shiftRight ne_40 (nat_lit 11)) (Nat.shiftLeft ne_40 (nat_lit 21)))) (Nat.lor (Nat.shiftRight ne_40 (nat_lit 25)) (Nat.shiftLeft ne_40 (nat_lit 7)))) (Nat.add (Nat.xor (Nat.land ne_40 ne_39) (Nat.land (Nat.xor ne_40 (nat_lit 4294967295)) ne_38)) (Nat.add (nat_lit 2820302411) w_41))))
  let na_41 := (Nat.land (Nat.add t1_41 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight na_40 (nat_lit 2)) (Nat.shiftLeft na_40 (nat_lit 30))) (Nat.lor (Nat.shiftRight na_40 (nat_lit 13)) (Nat.shiftLeft na_40 (nat_lit 19)))) (Nat.lor (Nat.shiftRight na_40 (nat_lit 22)) (Nat.shiftLeft na_40 (nat_lit 10)))) (Nat.xor (Nat.land na_40 (Nat.xor na_39 na_38)) (Nat.land na_39 na_38)))) (nat_lit 4294967295))
  let ne_41 := (Nat.land (Nat.add na_37 t1_41) (nat_lit 4294967295))
  let w_42 := (Nat.land (Nat.add (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight w_40 (nat_lit 17)) (Nat.shiftLeft w_40 (nat_lit 15))) (Nat.lor (Nat.shiftRight w_40 (nat_lit 19)) (Nat.shiftLeft w_40 (nat_lit 13)))) (Nat.shiftRight w_40 (nat_lit 10))) w_35) (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight w_27 (nat_lit 7)) (Nat.shiftLeft w_27 (nat_lit 25))) (Nat.lor (Nat.shiftRight w_27 (nat_lit 18)) (Nat.shiftLeft w_27 (nat_lit 14)))) (Nat.shiftRight w_27 (nat_lit 3))) w_26)) (nat_lit 4294967295))
  let t1_42 := (Nat.add ne_38 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight ne_41 (nat_lit 6)) (Nat.shiftLeft ne_41 (nat_lit 26))) (Nat.lor (Nat.shiftRight ne_41 (nat_lit 11)) (Nat.shiftLeft ne_41 (nat_lit 21)))) (Nat.lor (Nat.shiftRight ne_41 (nat_lit 25)) (Nat.shiftLeft ne_41 (nat_lit 7)))) (Nat.add (Nat.xor (Nat.land ne_41 ne_40) (Nat.land (Nat.xor ne_41 (nat_lit 4294967295)) ne_39)) (Nat.add (nat_lit 3259730800) w_42))))
  let na_42 := (Nat.land (Nat.add t1_42 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight na_41 (nat_lit 2)) (Nat.shiftLeft na_41 (nat_lit 30))) (Nat.lor (Nat.shiftRight na_41 (nat_lit 13)) (Nat.shiftLeft na_41 (nat_lit 19)))) (Nat.lor (Nat.shiftRight na_41 (nat_lit 22)) (Nat.shiftLeft na_41 (nat_lit 10)))) (Nat.xor (Nat.land na_41 (Nat.xor na_40 na_39)) (Nat.land na_40 na_39)))) (nat_lit 4294967295))
  let ne_42 := (Nat.land (Nat.add na_38 t1_42) (nat_lit 4294967295))
  let w_43 := (Nat.land (Nat.add (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight w_41 (nat_lit 17)) (Nat.shiftLeft w_41 (nat_lit 15))) (Nat.lor (Nat.shiftRight w_41 (nat_lit 19)) (Nat.shiftLeft w_41 (nat_lit 13)))) (Nat.shiftRight w_41 (nat_lit 10))) w_36) (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight w_28 (nat_lit 7)) (Nat.shiftLeft w_28 (nat_lit 25))) (Nat.lor (Nat.shiftRight w_28 (nat_lit 18)) (Nat.shiftLeft w_28 (nat_lit 14)))) (Nat.shiftRight w_28 (nat_lit 3))) w_27)) (nat_lit 4294967295))
  let t1_43 := (Nat.add ne_39 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight ne_42 (nat_lit 6)) (Nat.shiftLeft ne_42 (nat_lit 26))) (Nat.lor (Nat.shiftRight ne_42 (nat_lit 11)) (Nat.shiftLeft ne_42 (nat_lit 21)))) (Nat.lor (Nat.shiftRight ne_42 (nat_lit 25)) (Nat.shiftLeft ne_42 (nat_lit 7)))) (Nat.add (Nat.xor (Nat.land ne_42 ne_41) (Nat.land (Nat.xor ne_42 (nat_lit 4294967295)) ne_40)) (Nat.add (nat_lit 3345764771) w_43))))
  let na_43 := (Nat.land (Nat.add t1_43 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight na_42 (nat_lit 2)) (Nat.shiftLeft na_42 (nat_lit 30))) (Nat.lor (Nat.shiftRight na_42 (nat_lit 13)) (Nat.shiftLeft na_42 (nat_lit 19)))) (Nat.lor (Nat.shiftRight na_42 (nat_lit 22)) (Nat.shiftLeft na_42 (nat_lit 10)))) (Nat.xor (Nat.land na_42 (Nat.xor na_41 na_40)) (Nat.land na_41 na_40)))) (nat_lit 4294967295))
  let ne_43 := (Nat.land (Nat.add na_39 t1_43) (nat_lit 4294967295))
  let w_44 := (Nat.land (Nat.add (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight w_42 (nat_lit 17)) (Nat.shiftLeft w_42 (nat_lit 15))) (Nat.lor (Nat.shiftRight w_42 (nat_lit 19)) (Nat.shiftLeft w_42 (nat_lit 13)))) (Nat.shiftRight w_42 (nat_lit 10))) w_37) (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight w_29 (nat_lit 7)) (Nat.shiftLeft w_29 (nat_lit 25))) (Nat.lor (Nat.shiftRight w_29 (nat_lit 18)) (Nat.shiftLeft w_29 (nat_lit 14)))) (Nat.shiftRight w_29 (nat_lit 3))) w_28)) (nat_lit 4294967295))
  let t1_44 := (Nat.add ne_40 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight ne_43 (nat_lit 6)) (Nat.shiftLeft ne_43 (nat_lit 26))) (Nat.lor (Nat.shiftRight ne_43 (nat_lit 11)) (Nat.shiftLeft ne_43 (nat_lit 21)))) (Nat.lor (Nat.shiftRight ne_43 (nat_lit 25)) (Nat.shiftLeft ne_43 (nat_lit 7)))) (Nat.add (Nat.xor (Nat.land ne_43 ne_42) (Nat.land (Nat.xor ne_43 (nat_lit 4294967295)) ne_41)) (Nat.add (nat_lit 3516065817) w_44))))
  let na_44 := (Nat.land (Nat.add t1_44 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight na_43 (nat_lit 2)) (Nat.shiftLeft na_43 (nat_lit 30))) (Nat.lor (Nat.shiftRight na_43 (nat_lit 13)) (Nat.shiftLeft na_43 (nat_lit 19)))) (Nat.lor (Nat.shiftRight na_43 (nat_lit 22)) (Nat.shiftLeft na_43 (nat_lit 10)))) (Nat.xor (Nat.land na_43 (Nat.xor na_42 na_41)) (Nat.land na_42 na_41)))) (nat_lit 4294967295))
  let ne_44 := (Nat.land (Nat.add na_40 t1_44) (nat_lit 4294967295))
  let w_45 := (Nat.land (Nat.add (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight w_43 (nat_lit 17)) (Nat.shiftLeft w_43 (nat_lit 15))) (Nat.lor (Nat.shiftRight w_43 (nat_lit 19)) (Nat.shiftLeft w_43 (nat_lit 13)))) (Nat.shiftRight w_43 (nat_lit 10))) w_38) (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight w_30 (nat_lit 7)) (Nat.shiftLeft w_30 (nat_lit 25))) (Nat.lor (Nat.shiftRight w_30 (nat_lit 18)) (Nat.shiftLeft w_30 (nat_lit 14)))) (Nat.shiftRight w_30 (nat_lit 3))) w_29)) (nat_lit 4294967295))
  let t1_45 := (Nat.add ne_41 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight ne_44 (nat_lit 6)) (Nat.shiftLeft ne_44 (nat_lit 26))) (Nat.lor (Nat.shiftRight ne_44 (nat_lit 11)) (Nat.shiftLeft ne_44 (nat_lit 21)))) (Nat.lor (Nat.shiftRight ne_44 (nat_lit 25)) (Nat.shiftLeft ne_44 (nat_lit 7)))) (Nat.add (Nat.xor (Nat.land ne_44 ne_43) (Nat.land (Nat.xor ne_44 (nat_lit 4294967295)) ne_42)) (Nat.add (nat_lit 3600352804) w_45))))
  let na_45 := (Nat.land (Nat.add t1_45 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight na_44 (nat_lit 2)) (Nat.shiftLeft na_44 (nat_lit 30))) (Nat.lor (Nat.shiftRight na_44 (nat_lit 13)) (Nat.shiftLeft na_44 (nat_lit 19)))) (Nat.lor (Nat.shiftRight na_44 (nat_lit 22)) (Nat.shiftLeft na_44 (nat_lit 10)))) (Nat.xor (Nat.land na_44 (Nat.xor na_43 na_42)) (Nat.land na_43 na_42)))) (nat_lit 4294967295))
  let ne_45 := (Nat.land (Nat.add na_41 t1_45) (nat_lit 4294967295))
  let w_46 := (Nat.land (Nat.add (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight w_44 (nat_lit 17)) (Nat.shiftLeft w_44 (nat_lit 15))) (Nat.lor (Nat.shiftRight w_44 (nat_lit 19)) (Nat.shiftLeft w_44 (nat_lit 13)))) (Nat.shiftRight w_44 (nat_lit 10))) w_39) (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight w_31 (nat_lit 7)) (Nat.shiftLeft w_31 (nat_lit 25))) (Nat.lor (Nat.shiftRight w_31 (nat_lit 18)) (Nat.shiftLeft w_31 (nat_lit 14)))) (Nat.shiftRight w_31 (nat_lit 3))) w_30)) (nat_lit 4294967295))
  let t1_46 := (Nat.add ne_42 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight ne_45 (nat_lit 6)) (Nat.shiftLeft ne_45 (nat_lit 26))) (Nat.lor (Nat.shiftRight ne_45 (nat_lit 11)) (Nat.shiftLeft ne_45 (nat_lit 21)))) (Nat.lor (Nat.shiftRight ne_45 (nat_lit 25)) (Nat.shiftLeft ne_45 (nat_lit 7)))) (Nat.add (Nat.xor (Nat.land ne_45 ne_44) (Nat.land (Nat.xor ne_45 (nat_lit 4294967295)) ne_43)) (Nat.add (nat_lit 4094571909) w_46))))
  let na_46 := (Nat.land (Nat.add t1_46 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight na_45 (nat_lit 2)) (Nat.shiftLeft na_45 (nat_lit 30))) (Nat.lor (Nat.shiftRight na_45 (nat_lit 13)) (Nat.shiftLeft na_45 (nat_lit 19)))) (Nat.lor (Nat.shiftRight na_45 (nat_lit 22)) (Nat.shiftLeft na_45 (nat_lit 10)))) (Nat.xor (Nat.land na_45 (Nat.xor na_44 na_43)) (Nat.land na_44 na_43)))) (nat_lit 4294967295))
  let ne_46 := (Nat.land (Nat.add na_42 t1_46) (nat_lit 4294967295))
  let w_47 := (Nat.land (Nat.add (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight w_45 (nat_lit 17)) (Nat.shiftLeft w_45 (nat_lit 15))) (Nat.lor (Nat.shiftRight w_45 (nat_lit 19)) (Nat.shiftLeft w_45 (nat_lit 13)))) (Nat.shiftRight w_45 (nat_lit 10))) w_40) (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight w_32 (nat_lit 7)) (Nat.shiftLeft w_32 (nat_lit 25))) (Nat.lor (Nat.shiftRight w_32 (nat_lit 18)) (Nat.shiftLeft w_32 (nat_lit 14)))) (Nat.shiftRight w_32 (nat_lit 3))) w_31)) (nat_lit 4294967295))
  let t1_47 := (Nat.add ne_43 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight ne_46 (nat_lit 6)) (Nat.shiftLeft ne_46 (nat_lit 26))) (Nat.lor (Nat.shiftRight ne_46 (nat_lit 11)) (Nat.shiftLeft ne_46 (nat_lit 21)))) (Nat.lor (Nat.shiftRight ne_46 (nat_lit 25)) (Nat.shiftLeft ne_46 (nat_lit 7)))) (Nat.add (Nat.xor (Nat.land ne_46 ne_45) (Nat.land (Nat.xor ne_46 (nat_lit 4294967295)) ne_44)) (Nat.add (nat_lit 275423344) w_47))))
  let na_47 := (Nat.land (Nat.add t1_47 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight na_46 (nat_lit 2)) (Nat.shiftLeft na_46 (nat_lit 30))) (Nat.lor (Nat.shiftRight na_46 (nat_lit 13)) (Nat.shiftLeft na_46 (nat_lit 19)))) (Nat.lor (Nat.shiftRight na_46 (nat_lit 22)) (Nat.shiftLeft na_46 (nat_lit 10)))) (Nat.xor (Nat.land na_46 (Nat.xor na_45 na_44)) (Nat.land na_45 na_44)))) (nat_lit 4294967295))
  let ne_47 := (Nat.land (Nat.add na_43 t1_47) (nat_lit 4294967295))
  let w_48 := (Nat.land (Nat.add (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight w_46 (nat_lit 17)) (Nat.shiftLeft w_46 (nat_lit 15))) (Nat.lor (Nat.shiftRight w_46 (nat_lit 19)) (Nat.shiftLeft w_46 (nat_lit 13)))) (Nat.shiftRight w_46 (nat_lit 10))) w_41) (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight w_33 (nat_lit 7)) (Nat.shiftLeft w_33 (nat_lit 25))) (Nat.lor (Nat.shiftRight w_33 (nat_lit 18)) (Nat.shiftLeft w_33 (nat_lit 14)))) (Nat.shiftRight w_33 (nat_lit 3))) w_32)) (nat_lit 4294967295))
  let t1_48 := (Nat.add ne_44 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight ne_47 (nat_lit 6)) (Nat.shiftLeft ne_47 (nat_lit 26))) (Nat.lor (Nat.shiftRight ne_47 (nat_lit 11)) (Nat.shiftLeft ne_47 (nat_lit 21)))) (Nat.lor (Nat.shiftRight ne_47 (nat_lit 25)) (Nat.shiftLeft ne_47 (nat_lit 7)))) (Nat.add (Nat.xor (Nat.land ne_47 ne_46) (Nat.land (Nat.xor ne_47 (nat_lit 4294967295)) ne_45)) (Nat.add (nat_lit 430227734) w_48))))
  let na_48 := (Nat.land (Nat.add t1_48 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight na_47 (nat_lit 2)) (Nat.shiftLeft na_47 (nat_lit 30))) (Nat.lor (Nat.shiftRight na_47 (nat_lit 13)) (Nat.shiftLeft na_47 (nat_lit 19)))) (Nat.lor (Nat.shiftRight na_47 (nat_lit 22)) (Nat.shiftLeft na_47 (nat_lit 10)))) (Nat.xor (Nat.land na_47 (Nat.xor na_46 na_45)) (Nat.land na_46 na_45)))) (nat_lit 4294967295))
  let ne_48 := (Nat.land (Nat.add na_44 t1_48) (nat_lit 4294967295))
  let w_49 := (Nat.land (Nat.add (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight w_47 (nat_lit 17)) (Nat.shiftLeft w_47 (nat_lit 15))) (Nat.lor (Nat.shiftRight w_47 (nat_lit 19)) (Nat.shiftLeft w_47 (nat_lit 13)))) (Nat.shiftRight w_47 (nat_lit 10))) w_42) (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight w_34 (nat_lit 7)) (Nat.shiftLeft w_34 (nat_lit 25))) (Nat.lor (Nat.shiftRight w_34 (nat_lit 18)) (Nat.shiftLeft w_34 (nat_lit 14)))) (Nat.shiftRight w_34 (nat_lit 3))) w_33)) (nat_lit 4294967295))
  let t1_49 := (Nat.add ne_45 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight ne_48 (nat_lit 6)) (Nat.shiftLeft ne_48 (nat_lit 26))) (Nat.lor (Nat.shiftRight ne_48 (nat_lit 11)) (Nat.shiftLeft ne_48 (nat_lit 21)))) (Nat.lor (Nat.shiftRight ne_48 (nat_lit 25)) (Nat.shiftLeft ne_48 (nat_lit 7)))) (Nat.add (Nat.xor (Nat.land ne_48 ne_47) (Nat.land (Nat.xor ne_48 (nat_lit 4294967295)) ne_46)) (Nat.add (nat_lit 506948616) w_49))))
  let na_49 := (Nat.land (Nat.add t1_49 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight na_48 (nat_lit 2)) (Nat.shiftLeft na_48 (nat_lit 30))) (Nat.lor (Nat.shiftRight na_48 (nat_lit 13)) (Nat.shiftLeft na_48 (nat_lit 19)))) (Nat.lor (Nat.shiftRight na_48 (nat_lit 22)) (Nat.shiftLeft na_48 (nat_lit 10)))) (Nat.xor (Nat.land na_48 (Nat.xor na_47 na_46)) (Nat.land na_47 na_46)))) (nat_lit 4294967295))
  let ne_49 := (Nat.land (Nat.add na_45 t1_49) (nat_lit 4294967295))
  let w_50 := (Nat.land (Nat.add (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight w_48 (nat_lit 17)) (Nat.shiftLeft w_48 (nat_lit 15))) (Nat.lor (Nat.shiftRight w_48 (nat_lit 19)) (Nat.shiftLeft w_48 (nat_lit 13)))) (Nat.shiftRight w_48 (nat_lit 10))) w_43) (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight w_35 (nat_lit 7)) (Nat.shiftLeft w_35 (nat_lit 25))) (Nat.lor (Nat.shiftRight w_35 (nat_lit 18)) (Nat.shiftLeft w_35 (nat_lit 14)))) (Nat.shiftRight w_35 (nat_lit 3))) w_34)) (nat_lit 4294967295))
  let t1_50 := (Nat.add ne_46 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight ne_49 (nat_lit 6)) (Nat.shiftLeft ne_49 (nat_lit 26))) (Nat.lor (Nat.shiftRight ne_49 (nat_lit 11)) (Nat.shiftLeft ne_49 (nat_lit 21)))) (Nat.lor (Nat.shiftRight ne_49 (nat_lit 25)) (Nat.shiftLeft ne_49 (nat_lit 7)))) (Nat.add (Nat.xor (Nat.land ne_49 ne_48) (Nat.land (Nat.xor ne_49 (nat_lit 4294967295)) ne_47)) (Nat.add (nat_lit 659060556) w_50))))
  let na_50 := (Nat.land (Nat.add t1_50 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight na_49 (nat_lit 2)) (Nat.shiftLeft na_49 (nat_lit 30))) (Nat.lor (Nat.shiftRight na_49 (nat_lit 13)) (Nat.shiftLeft na_49 (nat_lit 19)))) (Nat.lor (Nat.shiftRight na_49 (nat_lit 22)) (Nat.shiftLeft na_49 (nat_lit 10)))) (Nat.xor (Nat.land na_49 (Nat.xor na_48 na_47)) (Nat.land na_48 na_47)))) (nat_lit 4294967295))
  let ne_50 := (Nat.land (Nat.add na_46 t1_50) (nat_lit 4294967295))
  let w_51 := (Nat.land (Nat.add (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight w_49 (nat_lit 17)) (Nat.shiftLeft w_49 (nat_lit 15))) (Nat.lor (Nat.shiftRight w_49 (nat_lit 19)) (Nat.shiftLeft w_49 (nat_lit 13)))) (Nat.shiftRight w_49 (nat_lit 10))) w_44) (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight w_36 (nat_lit 7)) (Nat.shiftLeft w_36 (nat_lit 25))) (Nat.lor (Nat.shiftRight w_36 (nat_lit 18)) (Nat.shiftLeft w_36 (nat_lit 14)))) (Nat.shiftRight w_36 (nat_lit 3))) w_35)) (nat_lit 4294967295))
  let t1_51 := (Nat.add ne_47 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight ne_50 (nat_lit 6)) (Nat.shiftLeft ne_50 (nat_lit 26))) (Nat.lor (Nat.shiftRight ne_50 (nat_lit 11)) (Nat.shiftLeft ne_50 (nat_lit 21)))) (Nat.lor (Nat.shiftRight ne_50 (nat_lit 25)) (Nat.shiftLeft ne_50 (nat_lit 7)))) (Nat.add (Nat.xor (Nat.land ne_50 ne_49) (Nat.land (Nat.xor ne_50 (nat_lit 4294967295)) ne_48)) (Nat.add (nat_lit 883997877) w_51))))
  let na_51 := (Nat.land (Nat.add t1_51 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight na_50 (nat_lit 2)) (Nat.shiftLeft na_50 (nat_lit 30))) (Nat.lor (Nat.shiftRight na_50 (nat_lit 13)) (Nat.shiftLeft na_50 (nat_lit 19)))) (Nat.lor (Nat.shiftRight na_50 (nat_lit 22)) (Nat.shiftLeft na_50 (nat_lit 10)))) (Nat.xor (Nat.land na_50 (Nat.xor na_49 na_48)) (Nat.land na_49 na_48)))) (nat_lit 4294967295))
  let ne_51 := (Nat.land (Nat.add na_47 t1_51) (nat_lit 4294967295))
  let w_52 := (Nat.land (Nat.add (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight w_50 (nat_lit 17)) (Nat.shiftLeft w_50 (nat_lit 15))) (Nat.lor (Nat.shiftRight w_50 (nat_lit 19)) (Nat.shiftLeft w_50 (nat_lit 13)))) (Nat.shiftRight w_50 (nat_lit 10))) w_45) (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight w_37 (nat_lit 7)) (Nat.shiftLeft w_37 (nat_lit 25))) (Nat.lor (Nat.shiftRight w_37 (nat_lit 18)) (Nat.shiftLeft w_37 (nat_lit 14)))) (Nat.shiftRight w_37 (nat_lit 3))) w_36)) (nat_lit 4294967295))
  let t1_52 := (Nat.add ne_48 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight ne_51 (nat_lit 6)) (Nat.shiftLeft ne_51 (nat_lit 26))) (Nat.lor (Nat.shiftRight ne_51 (nat_lit 11)) (Nat.shiftLeft ne_51 (nat_lit 21)))) (Nat.lor (Nat.shiftRight ne_51 (nat_lit 25)) (Nat.shiftLeft ne_51 (nat_lit 7)))) (Nat.add (Nat.xor (Nat.land ne_51 ne_50) (Nat.land (Nat.xor ne_51 (nat_lit 4294967295)) ne_49)) (Nat.add (nat_lit 958139571) w_52))))
  let na_52 := (Nat.land (Nat.add t1_52 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight na_51 (nat_lit 2)) (Nat.shiftLeft na_51 (nat_lit 30))) (Nat.lor (Nat.shiftRight na_51 (nat_lit 13)) (Nat.shiftLeft na_51 (nat_lit 19)))) (Nat.lor (Nat.shiftRight na_51 (nat_lit 22)) (Nat.shiftLeft na_51 (nat_lit 10)))) (Nat.xor (Nat.land na_51 (Nat.xor na_50 na_49)) (Nat.land na_50 na_49)))) (nat_lit 4294967295))
  let ne_52 := (Nat.land (Nat.add na_48 t1_52) (nat_lit 4294967295))
  let w_53 := (Nat.land (Nat.add (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight w_51 (nat_lit 17)) (Nat.shiftLeft w_51 (nat_lit 15))) (Nat.lor (Nat.shiftRight w_51 (nat_lit 19)) (Nat.shiftLeft w_51 (nat_lit 13)))) (Nat.shiftRight w_51 (nat_lit 10))) w_46) (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight w_38 (nat_lit 7)) (Nat.shiftLeft w_38 (nat_lit 25))) (Nat.lor (Nat.shiftRight w_38 (nat_lit 18)) (Nat.shiftLeft w_38 (nat_lit 14)))) (Nat.shiftRight w_38 (nat_lit 3))) w_37)) (nat_lit 4294967295))
  let t1_53 := (Nat.add ne_49 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight ne_52 (nat_lit 6)) (Nat.shiftLeft ne_52 (nat_lit 26))) (Nat.lor (Nat.shiftRight ne_52 (nat_lit 11)) (Nat.shiftLeft ne_52 (nat_lit 21)))) (Nat.lor (Nat.shiftRight ne_52 (nat_lit 25)) (Nat.shiftLeft ne_52 (nat_lit 7)))) (Nat.add (Nat.xor (Nat.land ne_52 ne_51) (Nat.land (Nat.xor ne_52 (nat_lit 4294967295)) ne_50)) (Nat.add (nat_lit 1322822218) w_53))))
  let na_53 := (Nat.land (Nat.add t1_53 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight na_52 (nat_lit 2)) (Nat.shiftLeft na_52 (nat_lit 30))) (Nat.lor (Nat.shiftRight na_52 (nat_lit 13)) (Nat.shiftLeft na_52 (nat_lit 19)))) (Nat.lor (Nat.shiftRight na_52 (nat_lit 22)) (Nat.shiftLeft na_52 (nat_lit 10)))) (Nat.xor (Nat.land na_52 (Nat.xor na_51 na_50)) (Nat.land na_51 na_50)))) (nat_lit 4294967295))
  let ne_53 := (Nat.land (Nat.add na_49 t1_53) (nat_lit 4294967295))
  let w_54 := (Nat.land (Nat.add (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight w_52 (nat_lit 17)) (Nat.shiftLeft w_52 (nat_lit 15))) (Nat.lor (Nat.shiftRight w_52 (nat_lit 19)) (Nat.shiftLeft w_52 (nat_lit 13)))) (Nat.shiftRight w_52 (nat_lit 10))) w_47) (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight w_39 (nat_lit 7)) (Nat.shiftLeft w_39 (nat_lit 25))) (Nat.lor (Nat.shiftRight w_39 (nat_lit 18)) (Nat.shiftLeft w_39 (nat_lit 14)))) (Nat.shiftRight w_39 (nat_lit 3))) w_38)) (nat_lit 4294967295))
  let t1_54 := (Nat.add ne_50 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight ne_53 (nat_lit 6)) (Nat.shiftLeft ne_53 (nat_lit 26))) (Nat.lor (Nat.shiftRight ne_53 (nat_lit 11)) (Nat.shiftLeft ne_53 (nat_lit 21)))) (Nat.lor (Nat.shiftRight ne_53 (nat_lit 25)) (Nat.shiftLeft ne_53 (nat_lit 7)))) (Nat.add (Nat.xor (Nat.land ne_53 ne_52) (Nat.land (Nat.xor ne_53 (nat_lit 4294967295)) ne_51)) (Nat.add (nat_lit 1537002063) w_54))))
  let na_54 := (Nat.land (Nat.add t1_54 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight na_53 (nat_lit 2)) (Nat.shiftLeft na_53 (nat_lit 30))) (Nat.lor (Nat.shiftRight na_53 (nat_lit 13)) (Nat.shiftLeft na_53 (nat_lit 19)))) (Nat.lor (Nat.shiftRight na_53 (nat_lit 22)) (Nat.shiftLeft na_53 (nat_lit 10)))) (Nat.xor (Nat.land na_53 (Nat.xor na_52 na_51)) (Nat.land na_52 na_51)))) (nat_lit 4294967295))
  let ne_54 := (Nat.land (Nat.add na_50 t1_54) (nat_lit 4294967295))
  let w_55 := (Nat.land (Nat.add (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight w_53 (nat_lit 17)) (Nat.shiftLeft w_53 (nat_lit 15))) (Nat.lor (Nat.shiftRight w_53 (nat_lit 19)) (Nat.shiftLeft w_53 (nat_lit 13)))) (Nat.shiftRight w_53 (nat_lit 10))) w_48) (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight w_40 (nat_lit 7)) (Nat.shiftLeft w_40 (nat_lit 25))) (Nat.lor (Nat.shiftRight w_40 (nat_lit 18)) (Nat.shiftLeft w_40 (nat_lit 14)))) (Nat.shiftRight w_40 (nat_lit 3))) w_39)) (nat_lit 4294967295))
  let t1_55 := (Nat.add ne_51 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight ne_54 (nat_lit 6)) (Nat.shiftLeft ne_54 (nat_lit 26))) (Nat.lor (Nat.shiftRight ne_54 (nat_lit 11)) (Nat.shiftLeft ne_54 (nat_lit 21)))) (Nat.lor (Nat.shiftRight ne_54 (nat_lit 25)) (Nat.shiftLeft ne_54 (nat_lit 7)))) (Nat.add (Nat.xor (Nat.land ne_54 ne_53) (Nat.land (Nat.xor ne_54 (nat_lit 4294967295)) ne_52)) (Nat.add (nat_lit 1747873779) w_55))))
  let na_55 := (Nat.land (Nat.add t1_55 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight na_54 (nat_lit 2)) (Nat.shiftLeft na_54 (nat_lit 30))) (Nat.lor (Nat.shiftRight na_54 (nat_lit 13)) (Nat.shiftLeft na_54 (nat_lit 19)))) (Nat.lor (Nat.shiftRight na_54 (nat_lit 22)) (Nat.shiftLeft na_54 (nat_lit 10)))) (Nat.xor (Nat.land na_54 (Nat.xor na_53 na_52)) (Nat.land na_53 na_52)))) (nat_lit 4294967295))
  let ne_55 := (Nat.land (Nat.add na_51 t1_55) (nat_lit 4294967295))
  let w_56 := (Nat.land (Nat.add (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight w_54 (nat_lit 17)) (Nat.shiftLeft w_54 (nat_lit 15))) (Nat.lor (Nat.shiftRight w_54 (nat_lit 19)) (Nat.shiftLeft w_54 (nat_lit 13)))) (Nat.shiftRight w_54 (nat_lit 10))) w_49) (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight w_41 (nat_lit 7)) (Nat.shiftLeft w_41 (nat_lit 25))) (Nat.lor (Nat.shiftRight w_41 (nat_lit 18)) (Nat.shiftLeft w_41 (nat_lit 14)))) (Nat.shiftRight w_41 (nat_lit 3))) w_40)) (nat_lit 4294967295))
  let t1_56 := (Nat.add ne_52 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight ne_55 (nat_lit 6)) (Nat.shiftLeft ne_55 (nat_lit 26))) (Nat.lor (Nat.shiftRight ne_55 (nat_lit 11)) (Nat.shiftLeft ne_55 (nat_lit 21)))) (Nat.lor (Nat.shiftRight ne_55 (nat_lit 25)) (Nat.shiftLeft ne_55 (nat_lit 7)))) (Nat.add (Nat.xor (Nat.land ne_55 ne_54) (Nat.land (Nat.xor ne_55 (nat_lit 4294967295)) ne_53)) (Nat.add (nat_lit 1955562222) w_56))))
  let na_56 := (Nat.land (Nat.add t1_56 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight na_55 (nat_lit 2)) (Nat.shiftLeft na_55 (nat_lit 30))) (Nat.lor (Nat.shiftRight na_55 (nat_lit 13)) (Nat.shiftLeft na_55 (nat_lit 19)))) (Nat.lor (Nat.shiftRight na_55 (nat_lit 22)) (Nat.shiftLeft na_55 (nat_lit 10)))) (Nat.xor (Nat.land na_55 (Nat.xor na_54 na_53)) (Nat.land na_54 na_53)))) (nat_lit 4294967295))
  let ne_56 := (Nat.land (Nat.add na_52 t1_56) (nat_lit 4294967295))
  let w_57 := (Nat.land (Nat.add (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight w_55 (nat_lit 17)) (Nat.shiftLeft w_55 (nat_lit 15))) (Nat.lor (Nat.shiftRight w_55 (nat_lit 19)) (Nat.shiftLeft w_55 (nat_lit 13)))) (Nat.shiftRight w_55 (nat_lit 10))) w_50) (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight w_42 (nat_lit 7)) (Nat.shiftLeft w_42 (nat_lit 25))) (Nat.lor (Nat.shiftRight w_42 (nat_lit 18)) (Nat.shiftLeft w_42 (nat_lit 14)))) (Nat.shiftRight w_42 (nat_lit 3))) w_41)) (nat_lit 4294967295))
  let t1_57 := (Nat.add ne_53 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight ne_56 (nat_lit 6)) (Nat.shiftLeft ne_56 (nat_lit 26))) (Nat.lor (Nat.shiftRight ne_56 (nat_lit 11)) (Nat.shiftLeft ne_56 (nat_lit 21)))) (Nat.lor (Nat.shiftRight ne_56 (nat_lit 25)) (Nat.shiftLeft ne_56 (nat_lit 7)))) (Nat.add (Nat.xor (Nat.land ne_56 ne_55) (Nat.land (Nat.xor ne_56 (nat_lit 4294967295)) ne_54)) (Nat.add (nat_lit 2024104815) w_57))))
  let na_57 := (Nat.land (Nat.add t1_57 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight na_56 (nat_lit 2)) (Nat.shiftLeft na_56 (nat_lit 30))) (Nat.lor (Nat.shiftRight na_56 (nat_lit 13)) (Nat.shiftLeft na_56 (nat_lit 19)))) (Nat.lor (Nat.shiftRight na_56 (nat_lit 22)) (Nat.shiftLeft na_56 (nat_lit 10)))) (Nat.xor (Nat.land na_56 (Nat.xor na_55 na_54)) (Nat.land na_55 na_54)))) (nat_lit 4294967295))
  let ne_57 := (Nat.land (Nat.add na_53 t1_57) (nat_lit 4294967295))
  let w_58 := (Nat.land (Nat.add (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight w_56 (nat_lit 17)) (Nat.shiftLeft w_56 (nat_lit 15))) (Nat.lor (Nat.shiftRight w_56 (nat_lit 19)) (Nat.shiftLeft w_56 (nat_lit 13)))) (Nat.shiftRight w_56 (nat_lit 10))) w_51) (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight w_43 (nat_lit 7)) (Nat.shiftLeft w_43 (nat_lit 25))) (Nat.lor (Nat.shiftRight w_43 (nat_lit 18)) (Nat.shiftLeft w_43 (nat_lit 14)))) (Nat.shiftRight w_43 (nat_lit 3))) w_42)) (nat_lit 4294967295))
  let t1_58 := (Nat.add ne_54 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight ne_57 (nat_lit 6)) (Nat.shiftLeft ne_57 (nat_lit 26))) (Nat.lor (Nat.shiftRight ne_57 (nat_lit 11)) (Nat.shiftLeft ne_57 (nat_lit 21)))) (Nat.lor (Nat.shiftRight ne_57 (nat_lit 25)) (Nat.shiftLeft ne_57 (nat_lit 7)))) (Nat.add (Nat.xor (Nat.land ne_57 ne_56) (Nat.land (Nat.xor ne_57 (nat_lit 4294967295)) ne_55)) (Nat.add (nat_lit 2227730452) w_58))))
  let na_58 := (Nat.land (Nat.add t1_58 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight na_57 (nat_lit 2)) (Nat.shiftLeft na_57 (nat_lit 30))) (Nat.lor (Nat.shiftRight na_57 (nat_lit 13)) (Nat.shiftLeft na_57 (nat_lit 19)))) (Nat.lor (Nat.shiftRight na_57 (nat_lit 22)) (Nat.shiftLeft na_57 (nat_lit 10)))) (Nat.xor (Nat.land na_57 (Nat.xor na_56 na_55)) (Nat.land na_56 na_55)))) (nat_lit 4294967295))
  let ne_58 := (Nat.land (Nat.add na_54 t1_58) (nat_lit 4294967295))
  let w_59 := (Nat.land (Nat.add (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight w_57 (nat_lit 17)) (Nat.shiftLeft w_57 (nat_lit 15))) (Nat.lor (Nat.shiftRight w_57 (nat_lit 19)) (Nat.shiftLeft w_57 (nat_lit 13)))) (Nat.shiftRight w_57 (nat_lit 10))) w_52) (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight w_44 (nat_lit 7)) (Nat.shiftLeft w_44 (nat_lit 25))) (Nat.lor (Nat.shiftRight w_44 (nat_lit 18)) (Nat.shiftLeft w_44 (nat_lit 14)))) (Nat.shiftRight w_44 (nat_lit 3))) w_43)) (nat_lit 4294967295))
  let t1_59 := (Nat.add ne_55 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight ne_58 (nat_lit 6)) (Nat.shiftLeft ne_58 (nat_lit 26))) (Nat.lor (Nat.shiftRight ne_58 (nat_lit 11)) (Nat.shiftLeft ne_58 (nat_lit 21)))) (Nat.lor (Nat.shiftRight ne_58 (nat_lit 25)) (Nat.shiftLeft ne_58 (nat_lit 7)))) (Nat.add (Nat.xor (Nat.land ne_58 ne_57) (Nat.land (Nat.xor ne_58 (nat_lit 4294967295)) ne_56)) (Nat.add (nat_lit 2361852424) w_59))))
  let na_59 := (Nat.land (Nat.add t1_59 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight na_58 (nat_lit 2)) (Nat.shiftLeft na_58 (nat_lit 30))) (Nat.lor (Nat.shiftRight na_58 (nat_lit 13)) (Nat.shiftLeft na_58 (nat_lit 19)))) (Nat.lor (Nat.shiftRight na_58 (nat_lit 22)) (Nat.shiftLeft na_58 (nat_lit 10)))) (Nat.xor (Nat.land na_58 (Nat.xor na_57 na_56)) (Nat.land na_57 na_56)))) (nat_lit 4294967295))
  let ne_59 := (Nat.land (Nat.add na_55 t1_59) (nat_lit 4294967295))
  let w_60 := (Nat.land (Nat.add (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight w_58 (nat_lit 17)) (Nat.shiftLeft w_58 (nat_lit 15))) (Nat.lor (Nat.shiftRight w_58 (nat_lit 19)) (Nat.shiftLeft w_58 (nat_lit 13)))) (Nat.shiftRight w_58 (nat_lit 10))) w_53) (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight w_45 (nat_lit 7)) (Nat.shiftLeft w_45 (nat_lit 25))) (Nat.lor (Nat.shiftRight w_45 (nat_lit 18)) (Nat.shiftLeft w_45 (nat_lit 14)))) (Nat.shiftRight w_45 (nat_lit 3))) w_44)) (nat_lit 4294967295))
  let t1_60 := (Nat.add ne_56 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight ne_59 (nat_lit 6)) (Nat.shiftLeft ne_59 (nat_lit 26))) (Nat.lor (Nat.shiftRight ne_59 (nat_lit 11)) (Nat.shiftLeft ne_59 (nat_lit 21)))) (Nat.lor (Nat.shiftRight ne_59 (nat_lit 25)) (Nat.shiftLeft ne_59 (nat_lit 7)))) (Nat.add (Nat.xor (Nat.land ne_59 ne_58) (Nat.land (Nat.xor ne_59 (nat_lit 4294967295)) ne_57)) (Nat.add (nat_lit 2428436474) w_60))))
  let na_60 := (Nat.land (Nat.add t1_60 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight na_59 (nat_lit 2)) (Nat.shiftLeft na_59 (nat_lit 30))) (Nat.lor (Nat.shiftRight na_59 (nat_lit 13)) (Nat.shiftLeft na_59 (nat_lit 19)))) (Nat.lor (Nat.shiftRight na_59 (nat_lit 22)) (Nat.shiftLeft na_59 (nat_lit 10)))) (Nat.xor (Nat.land na_59 (Nat.xor na_58 na_57)) (Nat.land na_58 na_57)))) (nat_lit 4294967295))
  let ne_60 := (Nat.land (Nat.add na_56 t1_60) (nat_lit 4294967295))
  let w_61 := (Nat.land (Nat.add (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight w_59 (nat_lit 17)) (Nat.shiftLeft w_59 (nat_lit 15))) (Nat.lor (Nat.shiftRight w_59 (nat_lit 19)) (Nat.shiftLeft w_59 (nat_lit 13)))) (Nat.shiftRight w_59 (nat_lit 10))) w_54) (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight w_46 (nat_lit 7)) (Nat.shiftLeft w_46 (nat_lit 25))) (Nat.lor (Nat.shiftRight w_46 (nat_lit 18)) (Nat.shiftLeft w_46 (nat_lit 14)))) (Nat.shiftRight w_46 (nat_lit 3))) w_45)) (nat_lit 4294967295))
  let t1_61 := (Nat.add ne_57 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight ne_60 (nat_lit 6)) (Nat.shiftLeft ne_60 (nat_lit 26))) (Nat.lor (Nat.shiftRight ne_60 (nat_lit 11)) (Nat.shiftLeft ne_60 (nat_lit 21)))) (Nat.lor (Nat.shiftRight ne_60 (nat_lit 25)) (Nat.shiftLeft ne_60 (nat_lit 7)))) (Nat.add (Nat.xor (Nat.land ne_60 ne_59) (Nat.land (Nat.xor ne_60 (nat_lit 4294967295)) ne_58)) (Nat.add (nat_lit 2756734187) w_61))))
  let na_61 := (Nat.land (Nat.add t1_61 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight na_60 (nat_lit 2)) (Nat.shiftLeft na_60 (nat_lit 30))) (Nat.lor (Nat.shiftRight na_60 (nat_lit 13)) (Nat.shiftLeft na_60 (nat_lit 19)))) (Nat.lor (Nat.shiftRight na_60 (nat_lit 22)) (Nat.shiftLeft na_60 (nat_lit 10)))) (Nat.xor (Nat.land na_60 (Nat.xor na_59 na_58)) (Nat.land na_59 na_58)))) (nat_lit 4294967295))
  let ne_61 := (Nat.land (Nat.add na_57 t1_61) (nat_lit 4294967295))
  let t1_62 := (Nat.add ne_58 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight ne_61 (nat_lit 6)) (Nat.shiftLeft ne_61 (nat_lit 26))) (Nat.lor (Nat.shiftRight ne_61 (nat_lit 11)) (Nat.shiftLeft ne_61 (nat_lit 21)))) (Nat.lor (Nat.shiftRight ne_61 (nat_lit 25)) (Nat.shiftLeft ne_61 (nat_lit 7)))) (Nat.add (Nat.xor (Nat.land ne_61 ne_60) (Nat.land (Nat.xor ne_61 (nat_lit 4294967295)) ne_59)) (Nat.add (nat_lit 3204031479) (Nat.land (Nat.add (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight w_60 (nat_lit 17)) (Nat.shiftLeft w_60 (nat_lit 15))) (Nat.lor (Nat.shiftRight w_60 (nat_lit 19)) (Nat.shiftLeft w_60 (nat_lit 13)))) (Nat.shiftRight w_60 (nat_lit 10))) w_55) (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight w_47 (nat_lit 7)) (Nat.shiftLeft w_47 (nat_lit 25))) (Nat.lor (Nat.shiftRight w_47 (nat_lit 18)) (Nat.shiftLeft w_47 (nat_lit 14)))) (Nat.shiftRight w_47 (nat_lit 3))) w_46)) (nat_lit 4294967295))))))
  let na_62 := (Nat.land (Nat.add t1_62 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight na_61 (nat_lit 2)) (Nat.shiftLeft na_61 (nat_lit 30))) (Nat.lor (Nat.shiftRight na_61 (nat_lit 13)) (Nat.shiftLeft na_61 (nat_lit 19)))) (Nat.lor (Nat.shiftRight na_61 (nat_lit 22)) (Nat.shiftLeft na_61 (nat_lit 10)))) (Nat.xor (Nat.land na_61 (Nat.xor na_60 na_59)) (Nat.land na_60 na_59)))) (nat_lit 4294967295))
  let ne_62 := (Nat.land (Nat.add na_58 t1_62) (nat_lit 4294967295))
  let t1_63 := (Nat.add ne_59 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight ne_62 (nat_lit 6)) (Nat.shiftLeft ne_62 (nat_lit 26))) (Nat.lor (Nat.shiftRight ne_62 (nat_lit 11)) (Nat.shiftLeft ne_62 (nat_lit 21)))) (Nat.lor (Nat.shiftRight ne_62 (nat_lit 25)) (Nat.shiftLeft ne_62 (nat_lit 7)))) (Nat.add (Nat.xor (Nat.land ne_62 ne_61) (Nat.land (Nat.xor ne_62 (nat_lit 4294967295)) ne_60)) (Nat.add (nat_lit 3329325298) (Nat.land (Nat.add (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight w_61 (nat_lit 17)) (Nat.shiftLeft w_61 (nat_lit 15))) (Nat.lor (Nat.shiftRight w_61 (nat_lit 19)) (Nat.shiftLeft w_61 (nat_lit 13)))) (Nat.shiftRight w_61 (nat_lit 10))) w_56) (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight w_48 (nat_lit 7)) (Nat.shiftLeft w_48 (nat_lit 25))) (Nat.lor (Nat.shiftRight w_48 (nat_lit 18)) (Nat.shiftLeft w_48 (nat_lit 14)))) (Nat.shiftRight w_48 (nat_lit 3))) w_47)) (nat_lit 4294967295))))))
  ⟨(Nat.land (Nat.add (nat_lit 1779033703) (Nat.land (Nat.add t1_63 (Nat.add (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight na_62 (nat_lit 2)) (Nat.shiftLeft na_62 (nat_lit 30))) (Nat.lor (Nat.shiftRight na_62 (nat_lit 13)) (Nat.shiftLeft na_62 (nat_lit 19)))) (Nat.lor (Nat.shiftRight na_62 (nat_lit 22)) (Nat.shiftLeft na_62 (nat_lit 10)))) (Nat.xor (Nat.land na_62 (Nat.xor na_61 na_60)) (Nat.land na_61 na_60)))) (nat_lit 4294967295))) (nat_lit 4294967295)), (Nat.land (Nat.add (nat_lit 3144134277) na_62) (nat_lit 4294967295)), (Nat.land (Nat.add (nat_lit 1013904242) na_61) (nat_lit 4294967295)), (Nat.land (Nat.add (nat_lit 2773480762) na_60) (nat_lit 4294967295)), (Nat.land (Nat.add (nat_lit 1359893119) (Nat.land (Nat.add na_59 t1_63) (nat_lit 4294967295))) (nat_lit 4294967295)), (Nat.land (Nat.add (nat_lit 2600822924) ne_62) (nat_lit 4294967295)), (Nat.land (Nat.add (nat_lit 528734635) ne_61) (nat_lit 4294967295)), (Nat.land (Nat.add (nat_lit 1541459225) ne_60) (nat_lit 4294967295))⟩

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
  (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight x (nat_lit 7)) (Nat.shiftLeft x (nat_lit 25))) (Nat.lor (Nat.shiftRight x (nat_lit 18)) (Nat.shiftLeft x (nat_lit 14)))) (Nat.shiftRight x (nat_lit 3)))

def smallSigma1U (x : Nat) : Nat :=
  (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight x (nat_lit 17)) (Nat.shiftLeft x (nat_lit 15))) (Nat.lor (Nat.shiftRight x (nat_lit 19)) (Nat.shiftLeft x (nat_lit 13)))) (Nat.shiftRight x (nat_lit 10)))

def bigSigma0U (x : Nat) : Nat :=
  (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight x (nat_lit 2)) (Nat.shiftLeft x (nat_lit 30))) (Nat.lor (Nat.shiftRight x (nat_lit 13)) (Nat.shiftLeft x (nat_lit 19)))) (Nat.lor (Nat.shiftRight x (nat_lit 22)) (Nat.shiftLeft x (nat_lit 10))))

def bigSigma1U (x : Nat) : Nat :=
  (Nat.xor (Nat.xor (Nat.lor (Nat.shiftRight x (nat_lit 6)) (Nat.shiftLeft x (nat_lit 26))) (Nat.lor (Nat.shiftRight x (nat_lit 11)) (Nat.shiftLeft x (nat_lit 21)))) (Nat.lor (Nat.shiftRight x (nat_lit 25)) (Nat.shiftLeft x (nat_lit 7))))

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
    (Nat.xor (Nat.land a (Nat.xor b c)) (Nat.land b c)) = maj a b c := by
  unfold maj
  rw [← Nat.and_xor_distrib_left]
  simp only [hxor_eq, hand_eq]

theorem w32_lit : w32 = (nat_lit 4294967295) := rfl

theorem chU_eq (e f g : Nat) :
    (Nat.xor (Nat.land e f) (Nat.land (Nat.xor e (nat_lit 4294967295)) g)) = ch e f g := by
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
      add32R h (Nat.add (bigSigma1U e) (Nat.add (Nat.xor (Nat.land e f) (Nat.land (Nat.xor e (nat_lit 4294967295)) g)) (Nat.add k w))) := rfl
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
  have h1 : Nat.land (t2U a b c) w32R = add32R (bigSigma0U a) (Nat.xor (Nat.land a (Nat.xor b c)) (Nat.land b c)) := rfl
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
