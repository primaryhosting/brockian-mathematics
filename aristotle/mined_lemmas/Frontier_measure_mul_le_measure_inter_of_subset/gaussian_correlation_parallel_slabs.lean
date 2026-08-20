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

theorem gaussian_correlation_parallel_slabs {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [OpensMeasurableSpace E]
    (μ : Measure E) [IsGaussian μ] (f : StrongDual ℝ E) (a b : ℝ) :
    μ {x | |f x| ≤ a} * μ {x | |f x| ≤ b} ≤ μ ({x | |f x| ≤ a} ∩ {x | |f x| ≤ b}) :=
  gaussian_correlation_preimage_dual μ f
    (measurableSet_le measurable_norm measurable_const)
    (measurableSet_le measurable_norm measurable_const)
    (isSymmConvex_abs_le a) (isSymmConvex_abs_le b)

end Reductions

end Frontier

