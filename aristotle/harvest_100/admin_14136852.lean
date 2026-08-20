import Mathlib

/-!
# E Eq Std Add Char
Category: Characters
Target: Brockian.Characters5.e_eq_stdAddChar
Verification: verified
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real

namespace Brockian
namespace Characters5

/-- A primitive fifth root of unity. -/
noncomputable def omega : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- The bespoke additive character mod 5 on the five-ray wheel. -/
noncomputable def e (k : ZMod 5) : ℂ := omega ^ k.val

/-- The bespoke character equals Mathlib's standard additive character mod 5. -/
theorem e_eq_stdAddChar (k : ZMod 5) : e k = ZMod.stdAddChar (N := 5) k := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]
  rw [e, omega, ← Complex.exp_nat_mul]
  push_cast
  congr 1
  ring

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

