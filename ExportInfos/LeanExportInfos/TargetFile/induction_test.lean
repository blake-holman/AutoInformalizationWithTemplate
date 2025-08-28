import Mathlib.Tactic

theorem l1 (n : ℕ) : 2 ^ (n + 1) ≥ 2 * (n + 1) := by
  induction' n with k kh
  . rw [zero_add, pow_one, mul_one]
  .
    have h1 : 2 ^ (k + 2) ≥ 4 * (k + 1) := by
      rw [pow_add, pow_two]
      have h1' : 4 = 2 * 2 := by norm_num
      rw [h1', mul_comm, ge_iff_le, mul_assoc, mul_assoc 2 2 (2 ^ k), mul_le_mul_iff_of_pos_left (by norm_num)]
      rw [pow_add, pow_one,ge_iff_le, mul_comm (2 ^ k)] at *
      exact kh
    have h2 : 4 * (k + 1) ≥ 2 * (k + 2) := by
      rw [mul_add, mul_add, mul_one, ge_iff_le]
      ring_nf
      simp
      induction' k with k' _
      . rw [zero_mul, zero_mul]
      . rw [mul_le_mul_iff_of_pos_left]
        . norm_num
        . norm_num
    exact ge_trans h1 h2
