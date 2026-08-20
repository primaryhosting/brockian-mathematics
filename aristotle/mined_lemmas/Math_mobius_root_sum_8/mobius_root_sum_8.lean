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

open Finset

/-- Any negation of a primitive 8-th root of unity is again a primitive 8-th root of unity.
Indeed, if `a` is primitive of order 8 then `a ^ 4 = -1`, so `-a = a ^ 5` and `5` is coprime
to `8`. -/

theorem mobius_root_sum_8 :
    ∑ ζ ∈ primitiveRoots 8 ℂ, ζ = (ArithmeticFunction.moebius 8 : ℂ) := by
  have hmu : (ArithmeticFunction.moebius 8 : ℂ) = 0 := by
    rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree (by decide)]
    norm_num
  rw [hmu]
  refine Finset.sum_involution (fun a _ => -a) (fun a _ => by ring) ?_ ?_ (fun a _ => neg_neg a)
  · intro a _ ha
    simpa using fun h => ha (by linear_combination -h / 2 : a = 0)
  · intro a ha
    rw [mem_primitiveRoots (by norm_num)] at ha ⊢
    exact neg_isPrimitiveRoot_eight a ha

end Math

