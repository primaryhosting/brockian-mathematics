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

open ArithmeticFunction

/-- One of the two primitive 6-th roots of unity, `exp (π i / 3) = (1 + i √3) / 2`. -/

lemma isPrimitiveRoot_six_of_sq_eq {z : ℂ} (hz : z ^ 2 = z - 1) : IsPrimitiveRoot z 6 := by
  have h3 : z ^ 3 = -1 := by linear_combination (z + 1) * hz
  have h4 : z ^ 4 = -z := by linear_combination z * h3
  have h5 : z ^ 5 = 1 - z := by linear_combination z ^ 2 * h3 - hz
  have h6 : z ^ 6 = 1 := by linear_combination (z ^ 3 - 1) * h3
  refine IsPrimitiveRoot.mk_of_lt z (by norm_num) h6 ?_
  intro l hl hl6
  interval_cases l
  · intro h
    rw [pow_one] at h
    rw [h] at hz
    norm_num at hz
  · intro h
    rw [hz] at h
    have hz2 : z = 2 := by linear_combination h
    rw [hz2] at hz
    norm_num at hz
  · rw [h3]
    norm_num
  · intro h
    rw [h4] at h
    have hz2 : z = -1 := by linear_combination -h
    rw [hz2] at hz
    norm_num at hz
  · intro h
    rw [h5] at h
    have hz2 : z = 0 := by linear_combination -h
    rw [hz2] at hz
    norm_num at hz

