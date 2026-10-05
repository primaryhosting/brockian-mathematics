/-
# Mobius Root Sum 2
Category: Pure Mathematics
Target: Math.mobius_root_sum_2
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Math

/-- The set of primitive `2`-nd roots of unity in `ℂ` is `{-1}`. -/
theorem primitiveRoots_two_complex : primitiveRoots 2 ℂ = {-1} := by
  ext z
  rw [mem_primitiveRoots (by norm_num), Finset.mem_singleton]
  constructor
  · intro h
    have hz := h.pow_eq_one
    have h2 : (z - 1) * (z + 1) = 0 := by linear_combination hz
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact absurd (by linear_combination h3) (h.ne_one one_lt_two)
    · linear_combination h3
  · rintro rfl
    exact IsPrimitiveRoot.neg_one 0 (by norm_num)

/-- The sum of the primitive `2`-nd roots of unity equals `μ 2 = -1`. -/
theorem mobius_root_sum_2 :
    ∑ z ∈ primitiveRoots 2 ℂ, z = (ArithmeticFunction.moebius 2 : ℂ) := by
  rw [primitiveRoots_two_complex]
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

