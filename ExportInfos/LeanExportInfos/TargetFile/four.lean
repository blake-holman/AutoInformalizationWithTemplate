import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Defs

open Nat

theorem exists_infinite_primes2 (n : ℕ) : ∃ p, n ≤ p ∧ Nat.Prime p := by
  let p := minFac (n ! + 1)
  have f1 : n ! + 1 ≠ 1 := Nat.ne_of_gt <| succ_lt_succ <| factorial_pos _
  have pp : Nat.Prime p := minFac_prime f1
  have np : n ≤ p :=
  le_of_not_ge fun h =>
  have h₁ : p ∣ n ! := dvd_factorial (minFac_pos _) h
  have h₂ : p ∣ 1 := (Nat.dvd_add_iff_right h₁).2 (minFac_dvd _)
  pp.not_dvd_one h₂
  exact ⟨p, np, pp⟩
