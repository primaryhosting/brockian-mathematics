/-
# Bekenstein Bound
Category: Frontier Phys
Target: Phys.bekenstein_bound
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

set_option grind.warning false

namespace Phys

/-- The Bekenstein bound expression `2 π k R E / (ℏ c)`: the maximal thermodynamic
entropy of a system of total energy `E` that fits inside a sphere of radius `R`,
where `k` is Boltzmann's constant, `hbar` the reduced Planck constant and `c` the
speed of light. -/

theorem bekensteinHawkingEntropy_eq_bound_schwarzschild
    (k M hbar c G R E A : ℝ)
    (hR : R = 2 * G * M / c ^ 2) (hE : E = M * c ^ 2) (hA : A = 4 * Real.pi * R ^ 2) :
    bekensteinHawkingEntropy k A hbar c G = bekensteinBoundValue k R E hbar c := by
  subst hA
  subst hE
  subst hR
  unfold bekensteinHawkingEntropy bekensteinBoundValue
  field_simp

end Phys

