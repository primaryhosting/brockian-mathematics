import Mathlib

/-!
# E Eq Std Add Char
Category: Characters
Target: Brockian.Characters5.e_eq_stdAddChar
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Classical

namespace Brockian
namespace Characters5

/-- The primitive fifth root of unity used for the five-ray wheel. -/
noncomputable def omega : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- The bespoke additive character on `ZMod 5`: `e k = ω ^ k.val`. -/
noncomputable def e (k : ZMod 5) : ℂ := omega ^ k.val

/-- The bespoke character equals Mathlib's standard additive character mod `5`. -/
theorem e_eq_stdAddChar (k : ZMod 5) : e k = ZMod.stdAddChar (N := 5) k := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply, e, omega, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- Consequence of `e_eq_stdAddChar`: `e` is additive-to-multiplicative, i.e. an additive
character, inherited from Mathlib's `AddChar` API. -/
theorem e_add (a b : ZMod 5) : e (a + b) = e a * e b := by
  simp only [e_eq_stdAddChar]
  exact AddChar.map_add_eq_mul ZMod.stdAddChar a b

/-- Consequence of `e_eq_stdAddChar`: `e 0 = 1`. -/
theorem e_zero : e 0 = 1 := by
  simp only [e_eq_stdAddChar]
  exact AddChar.map_zero_eq_one ZMod.stdAddChar

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

