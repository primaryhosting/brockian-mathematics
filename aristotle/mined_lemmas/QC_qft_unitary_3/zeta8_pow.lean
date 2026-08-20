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

namespace QC

open Complex

/-- The primitive 8-th root of unity raised to an integer power `d`,
written as `exp (2 π i d / 8)`. -/

lemma zeta8_pow (d : ℤ) (n : ℕ) : zeta8 d ^ n = zeta8 (n * d) := by
  rw [zeta8, zeta8, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

