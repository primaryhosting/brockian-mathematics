import Mathlib

/-!
# E Add
Category: Characters
Target: Brockian.Characters5.e_add
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open scoped BigOperators
open scoped Real
open scoped Classical

namespace Brockian
namespace Characters5

/-- A primitive fifth root of unity. -/
noncomputable def omega : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- The additive character `e` on `ZMod 5`. -/
noncomputable def e (j : ZMod 5) : ℂ := omega ^ j.val

theorem omega_pow_five : omega ^ 5 = 1 := by
  rw [omega, ← Complex.exp_nat_mul]
  have : (5 : ℂ) * (2 * (Real.pi : ℂ) * Complex.I / 5) = (2 * Real.pi * Complex.I) := by
    ring
  simp [this, Complex.exp_two_pi_mul_I]

theorem e_add (j k : ZMod 5) : e (j + k) = e j * e k := by
  rw [e, e, e, ← pow_add]
  have key : ∀ n : ℕ, omega ^ (n % 5) = omega ^ n := by
    intro n
    conv_rhs => rw [← Nat.div_add_mod n 5, pow_add, pow_mul, omega_pow_five, one_pow, one_mul]
  rw [ZMod.val_add j k, key]

end Characters5
end Brockian

#print axioms Brockian.Characters5.e_add

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

