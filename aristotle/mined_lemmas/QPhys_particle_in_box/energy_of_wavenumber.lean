import Mathlib

/-!
# Particle In Box
Category: Quantum Physics
Target: QPhys.particle_in_box
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Real

namespace QPhys

/-- The `n`-th stationary state of the infinite square well of width `L`:
`ψ_n(x) = sin (n π x / L)` (unnormalized). -/

theorem energy_of_wavenumber (hbar m L : ℝ) (hL : 0 < L) (hm : 0 < m) (n : ℕ) :
    hbar ^ 2 * ((n : ℝ) * Real.pi / L) ^ 2 / (2 * m) = E hbar m L n := by
  simp only [E, div_pow, mul_pow]
  field_simp

end QPhys

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

