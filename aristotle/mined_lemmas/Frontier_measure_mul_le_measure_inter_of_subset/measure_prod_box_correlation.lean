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

theorem measure_prod_box_correlation {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [MeasurableSpace E] [AddCommGroup F] [Module ℝ F] [MeasurableSpace F]
    (μ : Measure E) (ν : Measure F) [SFinite μ] [SFinite ν]
    {K₁ L₁ : Set E} {K₂ L₂ : Set F}
    (h₁ : μ K₁ * μ L₁ ≤ μ (K₁ ∩ L₁)) (h₂ : ν K₂ * ν L₂ ≤ ν (K₂ ∩ L₂)) :
    (μ.prod ν) (K₁ ×ˢ K₂) * (μ.prod ν) (L₁ ×ˢ L₂) ≤ (μ.prod ν) ((K₁ ×ˢ K₂) ∩ (L₁ ×ˢ L₂)) := by
  rw [Set.prod_inter_prod, Measure.prod_prod, Measure.prod_prod, Measure.prod_prod]
  calc μ K₁ * ν K₂ * (μ L₁ * ν L₂) = (μ K₁ * μ L₁) * (ν K₂ * ν L₂) := by ring
    _ ≤ μ (K₁ ∩ L₁) * ν (K₂ ∩ L₂) := mul_le_mul' h₁ h₂

/-- **A genuinely infinite/high-dimensional consequence of the base case.**
For a Gaussian measure `μ` on a Banach space `E` and a continuous linear functional `f`,
the correlation inequality holds for any two sets that are preimages under `f` of symmetric
convex subsets of `ℝ` (e.g. two parallel symmetric slabs). This is obtained by pushing `μ`
forward along `f`, which is a Gaussian measure on `ℝ`, and applying the one-dimensional case. -/
