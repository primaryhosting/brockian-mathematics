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

namespace Math

/-- `Complex.I` is a primitive 4-th root of unity. -/

theorem isPrimitiveRoot_neg_I : IsPrimitiveRoot (-Complex.I) 4 := by
  apply IsPrimitiveRoot.mk_of_lt _ (by norm_num)
  · simp [pow_succ, Complex.I_mul_I]
  · intro l hl hl4
    interval_cases l <;> simp [pow_succ, Complex.I_mul_I] <;> norm_num [Complex.ext_iff]

/-- The primitive 4-th roots of unity in `ℂ` are exactly `i` and `-i`. -/
