import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
open Real

theorem pi_lt_sqrtTwoAddSeries2 (n : ℕ) :
    π < (2 : ℝ) ^ (n + 1) * √(2 - sqrtTwoAddSeries 0 n) + 1 / (4 : ℝ) ^ n := by
  have : π < (√(2 - sqrtTwoAddSeries 0 n) / (2 : ℝ) + (1 : ℝ) / ((2 : ℝ) ^ n) ^ 3 / 4) * (2 : ℝ) ^ (n + 2) := by
    rw [← div_lt_iff (by norm_num), ← sin_pi_over_two_pow_succ]
    refine lt_of_lt_of_le (lt_add_of_sub_right_lt (sin_gt_sub_cube ?_ ?_)) ?_
    · apply div_pos pi_pos; apply pow_pos; norm_num
    · rw [div_le_iff']
      · refine le_trans pi_le_four ?_
        simp only [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, mul_one]
        apply pow_le_pow_right (by norm_num)
        apply le_add_of_nonneg_left; apply Nat.zero_le
      · apply pow_pos; norm_num
    apply add_le_add_left; rw [div_le_div_right (by norm_num)]
    rw [le_div_iff (by norm_num), ← mul_pow]
    refine le_trans ?_ (le_of_eq (one_pow 3)); apply pow_le_pow_left
    · apply le_of_lt; apply mul_pos
      · apply div_pos pi_pos; apply pow_pos; norm_num
      · apply pow_pos; norm_num
    · rw [← le_div_iff (by norm_num)]
      refine le_trans ((div_le_div_right ?_).mpr pi_le_four) ?_
      · apply pow_pos; norm_num
      · simp only [pow_succ', ← div_div, one_div]
        norm_num
  apply lt_of_lt_of_le this (le_of_eq _); rw [add_mul]; congr 1
  · ring
  simp only [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, div_div, ← pow_add]
  rw [one_div, one_div, inv_mul_eq_iff_eq_mul₀, eq_comm, mul_inv_eq_iff_eq_mul₀, ← pow_add]
  · rw [add_assoc, Nat.mul_succ, add_comm, add_comm n, add_assoc, mul_comm n]
  all_goals norm_num
