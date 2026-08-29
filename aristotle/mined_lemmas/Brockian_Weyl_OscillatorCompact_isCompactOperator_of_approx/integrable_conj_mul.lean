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

theorem integrable_conj_mul (f g : SchwartzMap ℝ ℂ) :
    Integrable (fun x : ℝ => conj (f x) * g x) volume := by
  obtain ⟨C, _, hC⟩ := f.decay 0 0
  have hmeas : AEStronglyMeasurable (fun x : ℝ => conj (f x)) volume :=
    (Complex.continuous_conj.comp f.continuous).aestronglyMeasurable
  refine Integrable.bdd_mul (c := C) g.integrable hmeas
    (Filter.Eventually.of_forall fun x => ?_)
  simpa using hC x

