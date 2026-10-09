/-! ### F15 probe: pentagonal stride lemmas (helpers PROVEN, full stride deferred)

The frozen `partition-euler-cons` scaffold has 11 sorries, all in the pentagonal
stride arithmetic. The `/2` in `g1 k = k*(3k-1)/2` defeats omega. The proven
route is to prove the PRE-DIVISION stride identity and derive the `/2` form:

    (k+1)*(3(k+1)-1) = k*(3k-1) + 2*(3k+1)

This file establishes the four key helper lemmas that the full stride needs.
All compile with `-DwarningAsError=false`. The remaining work is assembling
them into the full `stride_g1`/`stride_g2` calc chains — routine, not conceptual.

NEXT SESSION: use these helpers to close the 11 sorries in the scaffold, then
build `impl_correct` for `partition-euler-cons`.
-/

-- truncated-sub identity for the g1 stride (j ≥ 0)
theorem stride_sub_g1 (j : Nat) : 3*(j+1)-1+3 = 3*(j+1)+2 := by
  have hc := Nat.sub_add_cancel (show 1 ≤ 3*(j+1) from Nat.succ_le_succ (Nat.zero_le _))
  omega

-- linear tail for g1 stride: m*3 + (3m+2) = 2*(3m+1)
theorem g1_tail (m : Nat) : m*3 + (3*m+2) = 2*(3*m+1) := by
  have h6 : m*3 = 3*m := Nat.mul_comm m 3
  rw [h6]; omega

-- linear tail for g2 stride: m*3 + (3m+4) = 2*(3m+2)
theorem g2_tail (m : Nat) : m*3 + (3*m+4) = 2*(3*m+2) := by
  have h6 : m*3 = 3*m := Nat.mul_comm m 3
  rw [h6]; omega

-- base case of g1 stride (k=0)
theorem stride_g1_zero : (0+1)*(3*(0+1)-1) = 0*(3*0-1) + 2*(3*0+1) := by decide

-- base case of g2 stride (k=0)
theorem stride_g2_zero : (0+1)*(3*(0+1)+1) = 0*(3*0+1) + 2*(3*0+2) := by decide

-- intermediate: (m+1)*(3m+2) = m*(3m+2) + (3m+2)
theorem succ_mul_g1 (m : Nat) : (m+1)*(3*m+2) = m*(3*m+2) + (3*m+2) := by
  rw [Nat.succ_mul]

-- intermediate: 3*(m+1)-1 = 3*m+2
theorem g1_step (m : Nat) : 3*(m+1)-1 = 3*m+2 := by omega

-- intermediate: 3*(m+1) = 3*m+3
theorem g1_step3 (m : Nat) : 3*(m+1) = 3*m+3 := by omega
