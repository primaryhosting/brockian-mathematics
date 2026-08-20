import Mathlib
/-!
# Gaussian Correlation
Category: Frontier — Fields Medal Work
Target: Frontier.gaussian_correlation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

open MeasureTheory ProbabilityTheory

namespace Frontier

/-- A set is *symmetric convex* if it is convex and invariant under `x ↦ -x`. -/

theorem gaussian_correlation : GaussianCorrelationInequality ℝ := by
  intro μ hμ _
  have : IsProbabilityMeasure μ := hμ.toIsProbabilityMeasure μ
  exact hasGaussianCorrelation_real μ

/-- Non-vacuity of the main theorem: every centered real Gaussian `N(0, v)` satisfies the
hypotheses, hence the correlation inequality for symmetric convex sets. -/
