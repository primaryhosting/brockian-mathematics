/-
# Hawking Temperature
Category: Frontier Phys
Target: Phys.hawking_temperature
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Phys

/-- The Schwarzschild radius `r_s = 2 G M / c²` of a body of mass `M`. -/
noncomputable def schwarzschildRadius (G M c : ℝ) : ℝ := 2 * G * M / c ^ 2

/-- The surface gravity of a Schwarzschild black hole, `κ = c² / (2 r_s)`,
i.e. the Newtonian-type acceleration scale `c⁴ / (4 G M)` at the horizon. -/
noncomputable def surfaceGravity (G M c : ℝ) : ℝ :=
  c ^ 2 / (2 * schwarzschildRadius G M c)

/-- The Hawking (Unruh) temperature associated with a surface gravity `κ`:
`T = ℏ κ / (2 π c k)`, where `k` is Boltzmann's constant. -/
noncomputable def hawkingTemperatureOfSurfaceGravity (hbar c k kappa : ℝ) : ℝ :=
  hbar * kappa / (2 * Real.pi * c * k)

/-- The Hawking temperature of a Schwarzschild black hole of mass `M`. -/
noncomputable def hawkingTemperature (hbar c G M k : ℝ) : ℝ :=
  hawkingTemperatureOfSurfaceGravity hbar c k (surfaceGravity G M c)

/-- The surface gravity of a Schwarzschild black hole of mass `M` is `c⁴ / (4 G M)`. -/
theorem surfaceGravity_eq (G M c : ℝ) (hG : G ≠ 0) (hM : M ≠ 0) (hc : c ≠ 0) :
    surfaceGravity G M c = c ^ 4 / (4 * G * M) := by
  unfold surfaceGravity schwarzschildRadius
  field_simp
  ring

/-- **Hawking temperature of a Schwarzschild black hole.**
The temperature `T = ℏ κ / (2 π c k)` determined by the horizon surface gravity
`κ = c² / (2 r_s)` of a Schwarzschild black hole of mass `M` equals
`T = ℏ c³ / (8 π G M k)`. -/
theorem hawking_temperature (hbar c G M k : ℝ)
    (hc : c ≠ 0) (hG : G ≠ 0) (hM : M ≠ 0) :
    hawkingTemperature hbar c G M k = hbar * c ^ 3 / (8 * Real.pi * G * M * k) := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  unfold hawkingTemperature hawkingTemperatureOfSurfaceGravity
  rw [surfaceGravity_eq G M c hG hM hc]
  field_simp
  ring

end Phys

