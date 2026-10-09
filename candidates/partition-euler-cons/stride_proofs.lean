/-! ### F15 RESULT: pentagonal stride lemmas — PROVEN (core Lean 4.33.1, no Mathlib)

Three lemmas, each verified by a real `lake env lean` compile (exit 0, no sorry):

  1. `p_even_dg1`  : ∃ r, k*(3*k-1) = 2*r                    (parity, case-split k%2)
  2. `stride_pre`  : (k+1)*(3*(k+1)-1) = k*(3*k-1) + 2*(3*k+1)  (pre-division stride)
  3. `g1_succ`     : ((k+1)*(3*(k+1)-1))/2 = (k*(3*k-1))/2 + (3*k+1)  (scaffold target)

KEY TECHNIQUE (reusable for g2 and the remaining 8 sorries):
  the `/2` defeats omega, so prove the PRE-DIVISION identity, obtain the
  parity witness `∃ r, X = 2*r`, rewrite `X/2 → r` via `Nat.mul_div_right`,
  then cancel the factor 2 with `Nat.eq_of_mul_eq_mul_left` and close linearly.
  Every nonlinear product is expanded first with `Nat.succ_mul` / `Nat.mul_add`.

PITFALL (verified numerically before proving): the intermediate identity
  `(m+1)*(3*m+3) = (m+1)*(3*m-1) + (m+1)*4`
is FALSE at m=0 (3 ≠ 4) because of Nat truncated subtraction. The working
decomposition routes around it: `m*(3*m+5) = m*(3*m+2) + m*3`.
-/

-- 1. PARITY (proven earlier)
theorem p_even_dg1 (k : Nat) : ∃ r, k * (3 * k - 1) = 2 * r := by
  cases h2 : k % 2 with
  | zero =>
    have hdvd : 2 ∣ k := (Nat.dvd_iff_mod_eq_zero (n := k) (m := 2)).mpr h2
    obtain ⟨q, hq⟩ := hdvd
    refine ⟨q * (3*k-1), ?_⟩
    rw [hq, Nat.mul_assoc]
  | succ m =>
    have h1 : k % 2 = 1 := by omega
    obtain ⟨q, hk⟩ : ∃ q, k = 2*q+1 := by
      have hd := Nat.div_add_mod k 2
      refine ⟨k/2, ?_⟩
      omega
    subst hk
    refine ⟨(2*q+1)*(3*q+1), ?_⟩
    have h3 : 3*(2*q+1) = 6*q+3 := by omega
    rw [h3]
    have h4 : 6*q+3-1 = 2*(3*q+1) := by omega
    rw [h4, Nat.mul_left_comm]

-- 2. STRIDE pre-division (proven just now)
theorem stride_pre (k : Nat) : (k+1)*(3*(k+1)-1) = k*(3*k-1) + 2*(3*k+1) := by
  cases k with
  | zero => decide
  | succ m =>
      have h1 : 3*(m+1) = 3*m+3 := by omega
      have h2 : 3*(m+2) = 3*m+6 := by omega
      rw [h1, h2]
      have n1 : 3*m+6-1 = 3*m+5 := by omega
      have n2 : 3*m+3-1 = 3*m+2 := by omega
      have n3 : 3*m+3+1 = 3*m+4 := by omega
      rw [n1, n2, n3]
      have e1 : (m+2)*(3*m+5) = (m+1)*(3*m+5) + (3*m+5) := by rw [Nat.succ_mul]
      have e2 : (m+1)*(3*m+2) = m*(3*m+2) + (3*m+2) := by rw [Nat.succ_mul]
      rw [e1]
      have e3 : (m+1)*(3*m+5) = m*(3*m+5) + (3*m+5) := by rw [Nat.succ_mul]
      rw [e3]
      have e4 : m*(3*m+5) = m*(3*m+2) + m*3 := by
        have hb : 3*m+5 = 3*m+2+3 := by omega
        rw [hb, Nat.mul_add]
      rw [e4]
      omega

-- 3. g1_succ: combine parity + stride, cancel the /2
theorem g1_succ (k : Nat) : ((k+1)*(3*(k+1)-1))/2 = (k*(3*k-1))/2 + (3*k+1) := by
  obtain ⟨r1, hr1⟩ := p_even_dg1 k
  obtain ⟨r2, hr2⟩ := p_even_dg1 (k+1)
  -- rewrite the divisions away using the parity witnesses
  rw [hr1, hr2]
  rw [Nat.mul_div_right r1 (by decide), Nat.mul_div_right r2 (by decide)]
  -- goal is now linear: r2 = r1 + (3*k+1)
  have hs := stride_pre k
  rw [hr1, hr2] at hs
  -- hs : 2*r2 = 2*r1 + 2*(3*k+1)
  have hcancel : r2 = r1 + (3*k+1) := by
    have h : 2*r2 = 2*(r1 + (3*k+1)) := by
      rw [Nat.mul_add]
      exact hs
    have h2 := Nat.eq_of_mul_eq_mul_left (show (0:Nat) < 2 by decide) h
    omega
  omega
