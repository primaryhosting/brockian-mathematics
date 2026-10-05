import Mathlib

/-!
# Hawking Temperature
Category: Frontier Phys
Target: Phys.hawking_temperature
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

namespace Phys

/-- The Schwarzschild radius (event-horizon radius) of a body of mass `M`,
`r_s = 2 G M / c ^ 2`. -/

theorem hawkingTemperature_strictAnti (hbar c G k : ℝ) (hbar0 : 0 < hbar) (hc : 0 < c)
    (hG : 0 < G) (hk : 0 < k) {M₁ M₂ : ℝ} (hM₁ : 0 < M₁) (hM₁₂ : M₁ < M₂) :
    hawkingTemperature hbar c G M₂ k < hawkingTemperature hbar c G M₁ k := by
  have hM₂ : 0 < M₂ := lt_trans hM₁ hM₁₂
  rw [hawking_temperature hbar c G M₁ k hc hG hM₁ hk,
    hawking_temperature hbar c G M₂ k hc hG hM₂ hk]
  have hd₁ : 0 < 8 * Real.pi * G * M₁ * k := by positivity
  have hd₂ : 0 < 8 * Real.pi * G * M₂ * k := by positivity
  rw [div_lt_div_iff₀ hd₂ hd₁]
  have key : 0 < hbar * c ^ 3 * (8 * Real.pi * G * k) := by positivity
  nlinarith [mul_pos key (sub_pos.mpr hM₁₂)]

end Phys

#print axioms Phys.hawking_temperature

