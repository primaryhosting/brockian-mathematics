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

/-- The Schwarzschild radius `r_s = 2GM/c²` of a body of mass `M`,
with gravitational constant `G` and speed of light `c`. -/
noncomputable def schwarzschildRadius (G M c : ℝ) : ℝ := 2 * G * M / c ^ 2

/-- The surface gravity `κ = c²/(2 r_s)` at the horizon of a Schwarzschild black hole. -/
noncomputable def surfaceGravity (G M c : ℝ) : ℝ := c ^ 2 / (2 * schwarzschildRadius G M c)

/-- The Hawking temperature associated with a horizon of surface gravity `κ`,
namely `T = ℏ κ / (2 π c k)`, where `k` is Boltzmann's constant. -/
noncomputable def hawkingTemperatureOfSurfaceGravity (hbar c k kappa : ℝ) : ℝ :=
  hbar * kappa / (2 * Real.pi * c * k)

/-- **Hawking temperature of a Schwarzschild black hole.**

For positive gravitational constant `G`, speed of light `c`, Boltzmann constant `k`
and positive mass `M`, the surface gravity of the Schwarzschild horizon
(of radius `r_s = 2GM/c²`) is `κ = c⁴/(4GM)`, and hence the Hawking temperature
`T = ℏκ/(2πck)` equals

  `T = ℏ c³ / (8 π G M k)`. -/
theorem hawking_temperature
    (G M c hbar k : ℝ) (hG : 0 < G) (hM : 0 < M) (hc : 0 < c) (hk : 0 < k) :
    surfaceGravity G M c = c ^ 4 / (4 * G * M) ∧
      hawkingTemperatureOfSurfaceGravity hbar c k (surfaceGravity G M c)
        = hbar * c ^ 3 / (8 * Real.pi * G * M * k) := by
  have hkappa : surfaceGravity G M c = c ^ 4 / (4 * G * M) := by
    unfold surfaceGravity schwarzschildRadius
    rw [div_eq_div_iff (by positivity) (by positivity)]
    field_simp
    ring
  refine ⟨hkappa, ?_⟩
  rw [hawkingTemperatureOfSurfaceGravity, hkappa,
    div_eq_div_iff (by positivity) (by positivity)]
  field_simp
  ring

end Phys

