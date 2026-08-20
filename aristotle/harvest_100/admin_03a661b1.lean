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

namespace Brockian
namespace Characters5

/-- The primitive fifth root of unity `ω = exp(2πi/5)`. -/
noncomputable def omega : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- The bespoke additive character on `ZMod 5`, `e k = ω ^ k.val`. -/
noncomputable def e (k : ZMod 5) : ℂ := omega ^ k.val

/-- Key intermediate lemma: `e k` is the exponential `exp(2πi·k.val/5)`. -/
theorem e_eq_exp (k : ZMod 5) :
    e k = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (k.val : ℂ) / 5) := by
  rw [e, omega, ← Complex.exp_nat_mul]
  congr 1
  ring

/-- The bespoke character equals Mathlib's standard additive character mod 5. -/
theorem e_eq_stdAddChar (k : ZMod 5) : e k = ZMod.stdAddChar (N := 5) k := by
  rw [e_eq_exp, ZMod.stdAddChar_apply, ZMod.toCircle_apply]
  norm_num

end Characters5
end Brockian

#print axioms Brockian.Characters5.e_eq_stdAddChar

