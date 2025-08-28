import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Group.Int
import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.Ring.Int

theorem four_dvd_add_or_sub_of_odd2 {a b : ℤ} (ha : Odd a) (hb : Odd b) : 4 ∣ a + b ∨ 4 ∣ a - b := by
  obtain ⟨m, rfl⟩ := ha
  obtain ⟨n, rfl⟩ := hb
  obtain h | h := Int.even_or_odd (m + n)
  · right
    rw [Int.even_add, ← Int.even_sub] at h
    obtain ⟨k, hk⟩ := h
    convert dvd_mul_right 4 k using 1
    rw [eq_add_of_sub_eq hk, mul_add, add_assoc, add_sub_cancel_right, ← two_mul, ← mul_assoc]
    rfl
  · left
    obtain ⟨k, hk⟩ := h
    convert dvd_mul_right 4 (k + 1) using 1
    rw [eq_sub_of_add_eq hk, add_right_comm, ← add_sub, mul_add, mul_sub, add_assoc, add_assoc,
      sub_add, add_assoc, ← sub_sub (2 * n), sub_self, zero_sub, sub_neg_eq_add, ← mul_assoc,
      mul_add]
    rfl
