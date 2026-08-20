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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

open MeasureTheory ProbabilityTheory Set

/-- A set is *symmetric convex* if it is convex and invariant under `x ↦ -x`. -/

def GaussianCorrelationProperty (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] : Prop :=
  ∀ (μ : Measure E), IsGaussian μ → μ.map (fun x ↦ -x) = μ →
    ∀ K L : Set E, IsSymmConvex K → IsSymmConvex L → MeasurableSet K → MeasurableSet L →
      μ K * μ L ≤ μ (K ∩ L)

/-! ### The one-dimensional case -/

/-- A symmetric convex subset of `ℝ` containing `a` contains every point of absolute value
at most `|a|`. -/
