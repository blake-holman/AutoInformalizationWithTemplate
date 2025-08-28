import Mathlib.Tactic
import Mathlib.Algebra.Group.Even

theorem EvenCanDivTwo :
  ∀a : ℤ, (Even a → a % 2 == 0) := by
  intro a Even_a
  have a_eq_even : ∃ k, a = 2 * k :=by
    let ⟨k, hyp1⟩ := Even_a
    use k; rw [hyp1]; ring_nf
  let ⟨l,hyp2⟩ := a_eq_even
  rw [hyp2]
  simp
