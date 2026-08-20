/-
# Mobius Root Sum 2
Category: Pure Mathematics
Target: Math.mobius_root_sum_2
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Math

/-- The only primitive `2`-nd root of unity in `ℂ` is `-1`. -/
theorem isPrimitiveRoot_two_iff (x : ℂ) : IsPrimitiveRoot x 2 ↔ x = -1 := by
  constructor
  · intro h
    have h2 : x ^ 2 = 1 := h.pow_eq_one
    have h1 : x ≠ 1 := h.ne_one one_lt_two
    have hz : (x - 1) * (x + 1) = 0 := by linear_combination h2
    rcases mul_eq_zero.1 hz with h' | h'
    · exact absurd (sub_eq_zero.1 h') h1
    · linear_combination h'
  · rintro rfl
    exact IsPrimitiveRoot.neg_one _ (by norm_num)

/-- The set of primitive `2`-nd roots of unity in `ℂ` is `{-1}`. -/
theorem primitiveRoots_two_complex : primitiveRoots 2 ℂ = {-1} := by
  ext x
  rw [mem_primitiveRoots (by norm_num), Finset.mem_singleton, isPrimitiveRoot_two_iff]

/-- The sum of the primitive `2`-nd roots of unity equals `μ(2) = -1`. -/
theorem mobius_root_sum_2 :
    ∑ z ∈ primitiveRoots 2 ℂ, z = (ArithmeticFunction.moebius 2 : ℂ) := by
  rw [primitiveRoots_two_complex, Finset.sum_singleton,
    ArithmeticFunction.moebius_apply_prime Nat.prime_two]
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

