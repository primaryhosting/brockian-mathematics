import Mathlib

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

/-!
# BCS gap equation: existence of a nonzero gap for any attractive coupling

At zero temperature, in the standard BCS model with a constant density of states and a
Debye cut-off `ω > 0`, the gap equation reads

  `1 = g * ∫_0^ω dξ / sqrt(ξ² + Δ²)`,

where `g > 0` is the (attractive) dimensionless coupling `N(0)·V`.  The integral is
computed in closed form as `arsinh (ω / Δ)`, and the equation therefore always has the
strictly positive solution `Δ = ω / sinh (1 / g)` — the Cooper instability: *any*
attractive coupling, no matter how weak, binds a nonzero gap.
-/

namespace Frontier

/-- The BCS gap functional: `∫_0^ω dξ / sqrt(ξ² + Δ²)` (constant density of states,
zero temperature, Debye cut-off `ω`). -/

noncomputable def bcsGapIntegral (ω Δ : ℝ) : ℝ :=
  ∫ ξ in (0 : ℝ)..ω, (Real.sqrt (ξ ^ 2 + Δ ^ 2))⁻¹

/-- Closed form of the BCS gap integral: `∫_0^ω dξ / sqrt(ξ² + Δ²) = arsinh (ω / Δ)`
for a positive gap `Δ`. -/
