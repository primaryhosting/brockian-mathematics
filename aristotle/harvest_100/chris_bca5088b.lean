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
noncomputable def schwarzschildRadius (c G M : ℝ) : ℝ := 2 * G * M / c ^ 2

/-- The surface gravity at the horizon of a Schwarzschild black hole,
`κ = c ^ 2 / (2 r_s)`. -/
noncomputable def surfaceGravity (c G M : ℝ) : ℝ :=
  c ^ 2 / (2 * schwarzschildRadius c G M)

/-- The Hawking temperature of a Schwarzschild black hole, defined from the surface gravity
by the Hawking relation `T = ℏ κ / (2 π c k)` (`k` = Boltzmann's constant). -/
noncomputable def hawkingTemperature (hbar c G M k : ℝ) : ℝ :=
  hbar * surfaceGravity c G M / (2 * Real.pi * c * k)

/-- The surface gravity of a Schwarzschild black hole is `κ = c ^ 4 / (4 G M)`. -/
theorem surfaceGravity_eq (c G M : ℝ) (hc : 0 < c) (hG : 0 < G) (hM : 0 < M) :
    surfaceGravity c G M = c ^ 4 / (4 * G * M) := by
  have hc' : c ≠ 0 := ne_of_gt hc
  have hG' : G ≠ 0 := ne_of_gt hG
  have hM' : M ≠ 0 := ne_of_gt hM
  unfold surfaceGravity schwarzschildRadius
  field_simp
  ring

/-- **Hawking temperature of a Schwarzschild black hole.**

For a nonrotating, uncharged black hole of mass `M`, the temperature of the thermal radiation
emitted at its horizon is
`T = ℏ c ³ / (8 π G M k)`,
where `ℏ` is the reduced Planck constant, `c` the speed of light, `G` Newton's constant and
`k` Boltzmann's constant. -/
theorem hawking_temperature (hbar c G M k : ℝ) (hc : 0 < c) (hG : 0 < G) (hM : 0 < M)
    (hk : 0 < k) :
    hawkingTemperature hbar c G M k = hbar * c ^ 3 / (8 * Real.pi * G * M * k) := by
  have hc' : c ≠ 0 := ne_of_gt hc
  have hG' : G ≠ 0 := ne_of_gt hG
  have hM' : M ≠ 0 := ne_of_gt hM
  have hk' : k ≠ 0 := ne_of_gt hk
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  unfold hawkingTemperature
  rw [surfaceGravity_eq c G M hc hG hM]
  field_simp
  ring

/-- The Hawking temperature is inversely proportional to the mass: `T * M` is independent of `M`. -/
theorem hawkingTemperature_mul_mass (hbar c G M k : ℝ) (hc : 0 < c) (hG : 0 < G) (hM : 0 < M)
    (hk : 0 < k) :
    hawkingTemperature hbar c G M k * M = hbar * c ^ 3 / (8 * Real.pi * G * k) := by
  have hG' : G ≠ 0 := ne_of_gt hG
  have hM' : M ≠ 0 := ne_of_gt hM
  have hk' : k ≠ 0 := ne_of_gt hk
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  rw [hawking_temperature hbar c G M k hc hG hM hk]
  field_simp

/-- Heavier Schwarzschild black holes are colder: the Hawking temperature is strictly
decreasing in the mass (for positive `ℏ`). -/
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

