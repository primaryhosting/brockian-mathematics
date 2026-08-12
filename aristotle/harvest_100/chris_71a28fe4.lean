import Mathlib

namespace Math

open Finset

/-- The sum of the primitive 2-nd roots of unity in `ℂ` equals `μ(2) = -1`. -/
theorem mobius_root_sum_2 :
    ∑ z ∈ primitiveRoots 2 ℂ, z = (ArithmeticFunction.moebius 2 : ℂ) := by
  have h : primitiveRoots 2 ℂ = {(-1 : ℂ)} := by
    ext z
    rw [mem_primitiveRoots (by norm_num), Finset.mem_singleton]
    constructor
    · intro hz
      have h2 := hz.pow_eq_one
      have h1 : z ≠ 1 := fun h => by simpa [h] using hz.ne_one (by norm_num)
      have hfac : (z - 1) * (z + 1) = 0 := by linear_combination h2
      rcases mul_eq_zero.1 hfac with h | h
      · exact absurd (sub_eq_zero.1 h) h1
      · exact eq_neg_of_add_eq_zero_left h
    · rintro rfl
      exact IsPrimitiveRoot.neg_one 0 (by norm_num)
  rw [h]
  simp [ArithmeticFunction.moebius_apply_prime Nat.prime_two]

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

