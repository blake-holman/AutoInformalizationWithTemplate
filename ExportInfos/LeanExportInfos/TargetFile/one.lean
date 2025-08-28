import Mathlib.Algebra.Group.Even
import Mathlib.Data.Real.Basic

open Nat

theorem n8x_then_n4x (n : ℕ) : (∃a : ℕ, n = 8 * a) → (∃b : ℕ, n = 4 * b) := by
  intro ⟨a, h⟩
  refine Exists.intro (2 * a) ?q
  . rw [← mul_assoc]
    simp
    exact h
