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

namespace Frontier

open Real MeasureTheory intervalIntegral

/-- The BCS pairing integral
`∫₀^ω dξ / √(ξ² + Δ²)`, i.e. the right-hand side of the BCS gap equation for a
constant density of states, energy cutoff `ω` and gap parameter `Δ`. -/

lemma continuous_inv_sqrt_sq_add_sq {Delta : ℝ} (hD : 0 < Delta) :
    Continuous (fun x : ℝ => (Real.sqrt (x ^ 2 + Delta ^ 2))⁻¹) := by
  apply Continuous.inv₀
  · fun_prop
  · intro x; positivity

/-- Closed form of the BCS pairing integral: `∫₀^ω dξ/√(ξ²+Δ²) = arsinh (ω/Δ)`. -/
