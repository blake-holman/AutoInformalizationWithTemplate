import Mathlib.Data.Real.Basic
import Mathlib.Tactic

set_option trace.Meta.Tactic.simp.rewrite true

theorem inequiv_ab (a b : ℝ) :
  (a > 2 ∧ b > 3) → a*b + 6 > 3*a + 2*b := by
  intro ⟨alt2, blt3⟩
  rw [gt_iff_lt, ← sub_pos]
  have h1 : (a - 2) * (b - 3) = (a*b + 6) - (3*a + 2*b) := by
    ring
  rw [h1.symm]
  rw [mul_pos_iff]
  apply Or.symm
  right
  rw [gt_iff_lt, ← sub_pos] at alt2 blt3
  exact ⟨alt2, blt3⟩
