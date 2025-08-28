import Mathlib.Analysis.NormedSpace.Basic
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Analysis.NormedSpace.Real
open Metric Set Function Filter
open scoped NNReal Topology

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

theorem interior_closedBall2 (x : E) {r : ℝ} (hr : r ≠ 0) :
    interior (closedBall x r) = ball x r := by
  cases' hr.lt_or_lt with hr hr
  · rw [closedBall_eq_empty.2 hr, ball_eq_empty.2 hr.le, interior_empty]
  refine Subset.antisymm ?_ ball_subset_interior_closedBall
  intro y hy
  rcases (mem_closedBall.1 <| interior_subset hy).lt_or_eq with (hr | rfl)
  · exact hr
  set f : ℝ → E := fun c : ℝ => c • (y - x) + x
  suffices f ⁻¹' closedBall x (dist y x) ⊆ Icc (-1) 1 by
    have hfc : Continuous f := (continuous_id.smul continuous_const).add continuous_const
    have hf1 : (1 : ℝ) ∈ f ⁻¹' interior (closedBall x <| dist y x) := by simpa [f]
    have h1 : (1 : ℝ) ∈ interior (Icc (-1 : ℝ) 1) :=
      interior_mono this (preimage_interior_subset_interior_preimage hfc hf1)
    simp at h1
  intro c hc
  rw [mem_Icc, ← abs_le, ← Real.norm_eq_abs, ← mul_le_mul_right hr]
  simpa [f, dist_eq_norm, norm_smul] using hc
