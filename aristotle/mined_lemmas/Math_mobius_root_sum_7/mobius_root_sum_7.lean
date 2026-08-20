import Mathlib

open Finset Complex Polynomial

namespace Math

/-- The sum of the primitive 7-th roots of unity in `ℂ` is `-1`. -/

theorem mobius_root_sum_7 :
    ∑ z ∈ primitiveRoots 7 ℂ, z = (ArithmeticFunction.moebius 7 : ℂ) := by
  rw [sum_primitiveRoots_seven_eq_neg_one,
    ArithmeticFunction.moebius_apply_prime (by norm_num)]
  norm_num

end Math

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

