import Mathlib.Tactic

namespace ExtractionSmoke

def doubled (n : ℕ) := n + n

theorem double_add (n : ℕ) : doubled n = 2 * n := by
  unfold doubled
  rw [two_mul]

theorem two_cases (n : ℕ) : n = 0 ∨ 0 < n := by
  by_cases h : n = 0
  · exact Or.inl h
  · exact Or.inr (Nat.pos_of_ne_zero h)

end ExtractionSmoke
