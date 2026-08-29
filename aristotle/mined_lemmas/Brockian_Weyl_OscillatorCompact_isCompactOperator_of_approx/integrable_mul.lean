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

theorem integrable_mul (f g : SchwartzMap ℝ ℂ) :
    Integrable (fun x : ℝ => f x * g x) volume := by
  obtain ⟨C, _, hC⟩ := f.decay 0 0
  refine Integrable.bdd_mul (c := C) g.integrable f.continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  simpa using hC x

/-- **Integration by parts on the Schwartz space.** -/
