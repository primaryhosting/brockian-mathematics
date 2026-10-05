import Mathlib
/-!
# Mobius Root Sum 2
Category: Pure Mathematics
Target: Math.mobius_root_sum_2
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

open Finset

/-- The set of primitive `2`-th roots of unity in `ℂ` is `{-1}`. -/
theorem primitiveRoots_two_complex : primitiveRoots 2 ℂ = {(-1 : ℂ)} := by
  simp only [Finset.eq_singleton_iff_unique_mem, mem_primitiveRoots two_pos]
  exact ⟨IsPrimitiveRoot.neg_one 0 (by norm_num),
    fun x => IsPrimitiveRoot.eq_neg_one_of_two_right⟩

/-- The sum of the primitive `2`-th roots of unity equals `μ 2 = -1`. -/
theorem mobius_root_sum_2 :
    ∑ z ∈ primitiveRoots 2 ℂ, z = (ArithmeticFunction.moebius 2 : ℂ) := by
  rw [primitiveRoots_two_complex, Finset.sum_singleton]
  have : ArithmeticFunction.moebius 2 = -1 := by
    simpa using ArithmeticFunction.moebius_apply_prime Nat.prime_two
  rw [this]
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

