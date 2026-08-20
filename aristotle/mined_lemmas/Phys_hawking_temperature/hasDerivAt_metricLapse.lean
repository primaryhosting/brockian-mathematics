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

theorem hasDerivAt_metricLapse (G M c : ℝ) {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (metricLapse G M c) (2 * G * M / (c ^ 2 * r ^ 2)) r := by
  have h := ((hasDerivAt_inv hr).const_mul (2 * G * M / c ^ 2)).const_sub 1
  have hfun : (fun x : ℝ => 1 - 2 * G * M / c ^ 2 * x⁻¹) = metricLapse G M c := by
    funext x
    simp only [metricLapse, div_eq_mul_inv, mul_inv]
    ring
  rw [hfun] at h
  convert h using 1
  field_simp

/-- The surface gravity is `κ = (c²/2) f'(r_s)`, evaluated at the horizon. -/
