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

/-
# Sum E Mul
Category: Characters
Target: Brockian.Characters5.sum_e_mul
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Sum E Mul
Category: Characters
Target: Brockian.Characters5.sum_e_mul
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real

namespace Brockian.Characters5

/-- A primitive fifth root of unity. -/
noncomputable def omega : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- The standard additive character of `ZMod 5`, `e x = ω ^ x.val`. -/
noncomputable def e (x : ZMod 5) : ℂ := omega ^ x.val

theorem isPrimitiveRoot_omega : IsPrimitiveRoot omega 5 :=
  Complex.isPrimitiveRoot_exp 5 (by norm_num)

/-- The sum of all fifth roots of unity vanishes. -/
theorem sum_omega_pow : 1 + omega + omega ^ 2 + omega ^ 3 + omega ^ 4 = 0 := by
  have h := isPrimitiveRoot_omega.geom_sum_eq_zero (by norm_num)
  simpa [Finset.sum_range_succ] using h

/-- `e` agrees with Mathlib's standard additive character on `ZMod 5`. -/
theorem e_eq_stdAddChar (x : ZMod 5) : e x = ZMod.stdAddChar x := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply, e, omega, ← Complex.exp_nat_mul]
  ring_nf

/-- Additive-character orthogonality on `ZMod 5`:
`∑ x, e (a * x)` equals `5` when `a = 0` and `0` otherwise. -/
theorem sum_e_mul (a : ZMod 5) :
    ∑ x : ZMod 5, e (a * x) = if a = 0 then 5 else 0 := by
  have h : ∀ x : ZMod 5, e (a * x) = ZMod.stdAddChar (x * a) := by
    intro x
    rw [e_eq_stdAddChar, mul_comm]
  simp only [h]
  rw [AddChar.sum_mulShift a (ZMod.isPrimitive_stdAddChar 5)]
  simp [ZMod.card]

end Brockian.Characters5

