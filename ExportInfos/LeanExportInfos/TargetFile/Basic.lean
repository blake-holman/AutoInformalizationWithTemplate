import Mathlib.Algebra.Group.Even

theorem EvenAddEvenEqEven (a : ℕ) (b : ℕ) :
  (Even a ∧ Even b) → Even (a + b) := by
  intro ⟨⟨r1, h1⟩ , ⟨r2, h2⟩⟩
  have h1 : a + b = (r1 + r2) + (r1 + r2) := by
    rw [Nat.add_assoc, Nat.add_comm r2, ← Nat.add_assoc, ← Nat.add_assoc]
    rw [h1, h2]
    rw [← Nat.add_assoc]
  apply (Exists.intro (r1 + r2) )
  apply h1
