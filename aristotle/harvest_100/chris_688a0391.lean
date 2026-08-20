/-
# Omega Pow Five
Category: Characters
Target: Brockian.Characters5.omega_pow_five
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped Real

namespace Brockian.Characters5

/-- The Brockian ray rotation: the primitive fifth root of unity `e^{2πi/5}`. -/
noncomputable def omega : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

@[inherit_doc] notation "ω" => Brockian.Characters5.omega

/-- The Brockian ray rotation returns to the start after five steps. -/
theorem omega_pow_five : ω ^ 5 = 1 := by
  rw [omega, ← Complex.exp_nat_mul]
  rw [show (5 : ℕ) * (2 * (Real.pi : ℂ) * Complex.I / 5) = 2 * (Real.pi : ℂ) * Complex.I by
    push_cast; field_simp]
  simp

end Brockian.Characters5

#print axioms Brockian.Characters5.omega_pow_five

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

