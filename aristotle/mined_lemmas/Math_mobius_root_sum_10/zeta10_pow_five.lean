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

/-- A fixed primitive 10-th root of unity in `ℂ`. -/

theorem zeta10_pow_five : zeta10 ^ 5 = -1 := by
  have h10 : zeta10 ^ 10 = 1 := isPrimitiveRoot_zeta10.pow_eq_one
  have h5 : zeta10 ^ 5 ≠ 1 :=
    isPrimitiveRoot_zeta10.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
  have h : (zeta10 ^ 5 - 1) * (zeta10 ^ 5 + 1) = 0 := by linear_combination h10
  rcases mul_eq_zero.1 h with h' | h'
  · exact absurd (by linear_combination h') h5
  · linear_combination h'

/-- The four primitive 10-th roots of unity sum to `1`. -/
