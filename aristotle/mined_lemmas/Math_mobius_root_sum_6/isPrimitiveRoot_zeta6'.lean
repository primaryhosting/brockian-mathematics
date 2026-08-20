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

lemma isPrimitiveRoot_zeta6' : IsPrimitiveRoot zeta6' 6 := by
  refine isPrimitiveRoot_six_of_sq_eq ?_
  simp only [zeta6']
  linear_combination (-1 / 4 : ℂ) * sqrt_three_sq +
    (((Real.sqrt 3 : ℝ) : ℂ) ^ 2 / 4) * Complex.I_sq

