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

noncomputable def berryConnection {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ψ : ℝ × ℝ → H) (p : ℝ × ℝ) : ℝ × ℝ :=
  ((inner ℂ (ψ p) (fderiv ℝ ψ p (1, 0)) : ℂ).im,
    (inner ℂ (ψ p) (fderiv ℝ ψ p (0, 1)) : ℂ).im)

/-- The Berry curvature `F = ∂₁ A₂ - ∂₂ A₁` of a Berry connection `A : ℝ × ℝ → ℝ × ℝ`
on a two–dimensional parameter space. -/
