/-
# E Add
Category: Characters
Target: Brockian.Characters5.e_add
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

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian
namespace Characters5

/-- A primitive fifth root of unity. -/
noncomputable def omega : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

@[inherit_doc] scoped notation "ω" => Brockian.Characters5.omega

/-- The additive character `e` on `ZMod 5`, `e j = ω ^ j.val`. -/
noncomputable def e (j : ZMod 5) : ℂ := ω ^ j.val

theorem omega_pow_five : ω ^ 5 = 1 := by
  rw [omega, ← Complex.exp_nat_mul]
  have h : ((5 : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I / 5) = 2 * Real.pi * Complex.I := by
    push_cast
    ring
  rw [h, Complex.exp_two_pi_mul_I]

theorem e_add (j k : ZMod 5) : e (j + k) = e j * e k := by
  simp only [e, ← pow_add]
  have hv : (j + k).val = (j.val + k.val) % 5 := ZMod.val_add j k
  have hd : j.val + k.val = 5 * ((j.val + k.val) / 5) + (j.val + k.val) % 5 :=
    (Nat.div_add_mod _ _).symm
  have hpow : ω ^ (j.val + k.val) = ω ^ ((j.val + k.val) % 5) := by
    conv_lhs => rw [hd]
    rw [pow_add, pow_mul, omega_pow_five, one_pow, one_mul]
  rw [hv, hpow]

end Characters5
end Brockian

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

