import Mathlib.Data.Real.Irrational
import Mathlib.Tactic

theorem abeqzero (a b : ℤ) : (a + b * √2 = 0) → (a = 0 ∧ b = 0) := by
  intro h
  have beqzero : b = 0 := by
    by_contra bh
    push_neg at bh
    have sq : √2 = - a / b := by
      rw [eq_div_iff,← add_zero (-(a : ℝ)) ,add_eq_of_eq_neg_add]
      rw [neg_neg, h.symm, mul_comm]
      norm_num
      exact bh
    have sq2irr := irrational_sqrt_two
    rw [irrational_iff_ne_rational] at sq2irr
    have := sq2irr (-a) b
    rw [sq] at this
    simp at this
  rw [beqzero] at h
  norm_cast at h
  rw [zero_mul, add_zero, Int.cast_eq_zero] at h
  exact ⟨h, beqzero⟩
