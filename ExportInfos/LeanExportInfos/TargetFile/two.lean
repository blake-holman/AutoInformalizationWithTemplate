import Mathlib.Tactic
open Int

set_option trace.Meta.Tactic.simp.rewrite true

theorem ab_minus4_a2_plus_b2_8 (a b : Int) : ((-4) ∣ a ∧ (-4) ∣ b) → (8 ∣ a^2 + b^2) := by
  intro ⟨h1, h2⟩
  rcases h1 with ⟨k, h1'⟩
  let ⟨l, h2'⟩ := h2
  rw [h1', h2']
  rw [pow_two,pow_two]
  rw [neg_mul,neg_mul,neg_mul,neg_mul,mul_neg, neg_neg, mul_neg, neg_neg]
  rw [dvd_def]
  apply Exists.intro
  have h3 : 4 * k * (4 * k) + 4 * l * (4 * l) = 8 * (2 * k^2 + 2 * l^2) := by
    ring
  exact h3
