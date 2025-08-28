import Mathlib.Tactic

set_option trace.Meta.Tactic.simp.all true
theorem one : 1 + 1 = 2 :=by
  erw [Nat.add_succ, Nat.add_zero]

theorem two : x + x = 2 * x := by
  rw [two_mul]

namespace Test
def pow_rec (p : Nat) : Nat → Nat
  | 0 => 1
  | Nat.succ n => p * pow_rec p n
end Test
