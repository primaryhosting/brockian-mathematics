/-
  CompactCriterion.lean — an abstract compactness criterion: an operator whose
  unit-ball image is uniformly approximable by finite-dimensional subspaces is
  a compact operator.
-/
import Mathlib

open Metric Filter

namespace Brockian.Weyl.OscillatorCompact

/-- An operator whose closed-unit-ball image is uniformly approximable by
finite-dimensional subspaces is a compact operator. -/

theorem norm_sq_eq_integral (w : L2R) : ‖w‖ ^ 2 = ∫ x : ℝ, ‖w x‖ ^ 2 := by
  have h := MeasureTheory.L2.inner_def (𝕜 := ℂ) w w
  have h2 : (inner ℂ w w : ℂ) = ((∫ x : ℝ, ‖w x‖ ^ 2 : ℝ) : ℂ) := by
    rw [h, ← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [RCLike.inner_apply]
    rw [mul_comm, RCLike.conj_mul]
    norm_cast
  have h3 : RCLike.re (inner ℂ w w : ℂ) = ‖w‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) w
  rw [h2] at h3
  simpa using h3.symm

