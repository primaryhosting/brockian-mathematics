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

theorem hasGaussianCorrelation_map {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [MeasurableSpace E] [AddCommGroup F] [Module ℝ F] [MeasurableSpace F]
    {μ : Measure E} (hμ : HasGaussianCorrelation μ) (T : E →ₗ[ℝ] F) (hT : Measurable T) :
    HasGaussianCorrelation (μ.map T) := by
  intro K L hKm hLm hK hL
  rw [Measure.map_apply hT hKm, Measure.map_apply hT hLm,
    Measure.map_apply hT (hKm.inter hLm), Set.preimage_inter]
  exact hμ _ _ (hKm.preimage hT) (hLm.preimage hT)
    (hK.preimage_linearMap T) (hL.preimage_linearMap T)

/-- Products of symmetric convex sets are symmetric convex. -/
