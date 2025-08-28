import Mathlib.Data.Real.Basic
import Mathlib.Tactic

theorem arith_geom_mean (a b : ℝ) (ha : a > 0) (hb : b > 0) : a + b ≥ 2 * √(a * b) := by
  rw [ge_iff_le]
  apply le_of_sub_nonneg
  have : a + b - 2 * √(a * b) = (√a - √b)^2 := by
    rw [sub_pow_two, Real.sq_sqrt (le_of_lt (gt_iff_lt.mp ha)), Real.sq_sqrt (le_of_lt (gt_iff_lt.mp hb)), Real.sqrt_mul (le_of_lt (gt_iff_lt.mp ha))]
    ring
  rw [this]
  exact pow_two_nonneg (√a - √b)

theorem l1 (a b : ℝ): (∀ε > 0, a < b + ε) → (a ≤ b) := by
  intro h
  by_contra! ih
  let δ := a - b
  have δpos : δ > 0 := by
    simp [δ]
    exact ih
  have abeq : a = b + δ := by
    simp [δ]
  have h1 : b + δ > b + δ / 2 := by
    simp
    exact δpos
  rw [abeq.symm] at h1
  have h2 := h (δ / 2) (half_pos δpos)
  linarith

theorem l2 (a b : ℝ) (ha : a > 0) (hb : b > 0) (hA : A = a + 4*b) (hB : B = 9 / a + 1 / b) : A ≥ 5 ∨ B ≥ 5 := by
  by_contra! h
  have : A + B < 10 := by
    have := add_lt_add h.left h.right
    ring_nf at this
    exact this
  have h2 : A + B = (a + 9 / a) + (4 * b + 1 / b) := by
    rw [hA, hB]
    ring
  have h3 : a + 9 / a ≥ 6 := by
    have h3' := arith_geom_mean a (9 / a) ha (by norm_num; exact ha)
    have h3'1 : √(a * (9 / a)) = 3 := by
      ring_nf
      simp
      rw [mul_inv_cancel ((lt_iff_le_and_ne.mp (gt_iff_lt.mp ha)).right.symm), Real.sqrt_one, one_mul, Real.sqrt_eq_iff_mul_self_eq_of_pos (by norm_num)]
      ring
    rw [h3'1] at h3'
    ring_nf at h3' ⊢
    exact h3'
  have h4 : 4 * b + 1 / b ≥ 4 := by
    have h4' := arith_geom_mean (4 * b) (1 / b) (by norm_num; exact hb) (by norm_num; exact hb)
    have h4'1 : √(4 * b * (1 / b)) = 2 := by
      ring_nf
      simp
      rw [mul_inv_cancel ((lt_iff_le_and_ne.mp (gt_iff_lt.mp hb)).right.symm), Real.sqrt_one, one_mul, Real.sqrt_eq_iff_mul_self_eq_of_pos (by norm_num)]
      ring
    rw [h4'1] at h4'
    ring_nf at h4' ⊢
    exact h4'
  have : A + B ≥ 10 := by
    rw [h2]
    rw [ge_iff_le] at h3 h4 ⊢
    have := add_le_add h3 h4
    ring_nf at this ⊢
    exact this
  linarith
