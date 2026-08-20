import Mathlib
/-!
# Berry Phase Quantized
Category: Frontier Physics
Target: Frontier.berry_phase_quantized
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

open MeasureTheory Set intervalIntegral

/-- The Berry connection of a family of quantum states `ψ : ℝ × ℝ → H` over a two–dimensional
parameter space, given in components by `A_j (R) = Im ⟪ψ R, ∂_j ψ R⟫`. -/

theorem berry_phase_quantized_of_states {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (ψ : ℝ × ℝ → H) (hψ : ContDiff ℝ 1 (berryConnection ψ))
    (a₁ a₂ b₁ b₂ : ℝ) :
    berryPhaseRect (berryConnection ψ) a₁ a₂ b₁ b₂ =
      ∫ x in a₁..b₁, ∫ y in a₂..b₂, berryCurvature (berryConnection ψ) (x, y) :=
  berry_phase_quantized _ hψ a₁ a₂ b₁ b₂

end Frontier

