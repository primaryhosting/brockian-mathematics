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

theorem schwartz_norm_mul_integrable (f g : SchwartzMap ℝ ℂ) :
    Integrable (fun x => ‖f x‖ * ‖g x‖) volume := by
  obtain ⟨C, _, hC⟩ := f.decay 0 0
  refine Integrable.bdd_mul (c := C) g.integrable.norm
    f.continuous.norm.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
  simpa using hC x

