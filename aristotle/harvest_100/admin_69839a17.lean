/-
# Mobius Root Sum 2
Category: Pure Mathematics
Target: Math.mobius_root_sum_2
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Mobius Root Sum 2
Category: Pure Mathematics
Target: Math.mobius_root_sum_2
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The sum of the primitive `2`-th roots of unity in `ℂ` equals `μ 2 = -1`. -/
theorem mobius_root_sum_2 :
    ∑ z ∈ primitiveRoots 2 ℂ, z = (ArithmeticFunction.moebius 2 : ℂ) := by
  have h : primitiveRoots 2 ℂ = {-1} := by
    ext z
    rw [mem_primitiveRoots (by norm_num), Finset.mem_singleton]
    constructor
    · intro hz
      have h1 := hz.pow_eq_one
      have h2 : (z - 1) * (z + 1) = 0 := by linear_combination h1
      rcases mul_eq_zero.1 h2 with h | h
      · exact absurd (by linear_combination h : z = 1) (hz.ne_one (by norm_num))
      · linear_combination h
    · rintro rfl
      exact IsPrimitiveRoot.neg_one 0 (by norm_num)
  rw [h, Finset.sum_singleton, ArithmeticFunction.moebius_apply_prime Nat.prime_two]
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

