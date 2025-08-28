import Mathlib.Tactic

open Nat


theorem test (P Q R: α → Prop) : (∀x : α, (P x → P x) → (Q x → R x)) → (∀x : α, (Q x → R x)):= by
  intro hyp
  by_contra h
  push_neg at h
  let ⟨x, h'⟩ := h
  let hyp' := hyp x
  have : P x → P x := by
    intro k; exact k
  exact h'.right (hyp' this h'.left)
