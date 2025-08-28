import Mathlib.Algebra.Group.Even
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Group.Int
import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.Ring.Int
import Mathlib.Tactic

theorem l1 (n : ℤ) : Even (n ^ 2) → Even n := by
  intro h
  by_contra ih
  have h' := Int.even_iff_not_odd.mp h
  let ⟨k, kh⟩ := Int.odd_iff_not_even.mpr ih
  have h1 : n ^ 2 = 2 * (2 * k ^ 2 + 2 * k) + 1 := by
    rw [kh, add_pow_two, pow_two, mul_one, one_pow, ← add_mul]
    ring
  have h2 : Odd (n^2) := ⟨(2 * k ^ 2 + 2 * k), h1⟩
  contradiction
