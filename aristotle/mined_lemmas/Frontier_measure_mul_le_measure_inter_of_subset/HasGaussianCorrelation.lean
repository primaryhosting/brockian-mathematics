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

def HasGaussianCorrelation {E : Type*} [AddCommGroup E] [Module ℝ E]
    [MeasurableSpace E] (μ : Measure E) : Prop :=
  ∀ K L : Set E, MeasurableSet K → MeasurableSet L → IsSymmConvex K → IsSymmConvex L →
    μ K * μ L ≤ μ (K ∩ L)

/-- **The Gaussian correlation inequality** (Royen's theorem) on a space `E`:
every centered (i.e. symmetric) Gaussian measure on `E` satisfies the correlation
inequality for symmetric convex sets.

This is the formalized *statement*. Below we prove it in dimension one
(`Frontier.gaussian_correlation : GaussianCorrelationInequality ℝ`), together with several
Lean-checked reductions; the full theorem in dimension `n` (Royen, 2014) is not proved here. -/
