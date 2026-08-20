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

theorem hasGaussianCorrelation_real (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    HasGaussianCorrelation μ := fun _K _L _ _ hK hL =>
  measure_mul_le_measure_inter_of_subset μ (symmConvex_subset_total hK hL)

/-- **The Gaussian correlation inequality in dimension one.** -/
