/-
# Hawking Temperature
Category: Frontier Phys
Target: Phys.hawking_temperature
Statement: State the Hawking temperature T = ℏc³/(8πGMk) of a Schwarzschild black hole.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Hawking Temperature
Category: Frontier Phys
Target: Phys.hawking_temperature
Statement: State the Hawking temperature T = ℏc³/(8πGMk) of a Schwarzschild black hole.
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

/-- The lapse function `f(r) = 1 - 2GM/(c²r)` of the Schwarzschild metric
`ds² = -f(r) c² dt² + f(r)⁻¹ dr² + r² dΩ²` for a black hole of mass `M`. -/

theorem surfaceGravity_eq_lapse_deriv {G M c : ℝ} (hG : G ≠ 0) (hM : M ≠ 0) (hc : c ≠ 0) :
    surfaceGravity G M c
      = c ^ 2 / 2 * deriv (metricLapse G M c) (schwarzschildRadius G M c) := by
  have hrs : schwarzschildRadius G M c ≠ 0 := by
    simp only [schwarzschildRadius]
    intro h
    rcases (div_eq_zero_iff.mp h) with h' | h'
    · rcases mul_eq_zero.mp h' with h'' | h''
      · rcases mul_eq_zero.mp h'' with h3 | h3
        · norm_num at h3
        · exact hG h3
      · exact hM h''
    · exact hc (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h')
  rw [(hasDerivAt_metricLapse G M c hrs).deriv]
  simp only [schwarzschildRadius, surfaceGravity]
  have h2 : (2 : ℝ) * G * M ≠ 0 := by simp [hG, hM]
  field_simp
  ring

/-- **Hawking temperature of a Schwarzschild black hole.**

For a black hole of mass `M`, the horizon surface gravity is `κ = c⁴/(4GM)`, and the
associated thermal (Hawking) temperature `T = ℏκ/(2πck)` is

`T = ℏc³/(8πGMk)`,

where `ℏ` is the reduced Planck constant, `c` the speed of light, `G` Newton's constant
and `k` Boltzmann's constant. -/
