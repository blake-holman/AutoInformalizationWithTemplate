import Mathlib.Tactic

example (a b: Nat) (h : a = b) : 8 * a = 16 / 2 * b  :=by
  norm_num
  exact?
