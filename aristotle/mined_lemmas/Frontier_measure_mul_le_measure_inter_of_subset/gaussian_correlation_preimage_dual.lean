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

theorem gaussian_correlation_preimage_dual {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [OpensMeasurableSpace E]
    (μ : Measure E) [IsGaussian μ] (f : StrongDual ℝ E) {A B : Set ℝ}
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAc : IsSymmConvex A) (hBc : IsSymmConvex B) :
    μ (f ⁻¹' A) * μ (f ⁻¹' B) ≤ μ (f ⁻¹' A ∩ f ⁻¹' B) := by
  have hf : Measurable f := f.continuous.measurable
  have hmap : μ.map f = gaussianReal (μ[f]) (Var[f; μ]).toNNReal :=
    IsGaussian.map_eq_gaussianReal f
  have hprob : IsProbabilityMeasure (μ.map f) := by
    rw [hmap]; infer_instance
  have := hasGaussianCorrelation_real (μ.map f) A B hA hB hAc hBc
  rwa [Measure.map_apply hf hA, Measure.map_apply hf hB,
    Measure.map_apply hf (hA.inter hB), Set.preimage_inter] at this

/-- Symmetric closed intervals `{t | |t| ≤ a}` are symmetric convex. -/
