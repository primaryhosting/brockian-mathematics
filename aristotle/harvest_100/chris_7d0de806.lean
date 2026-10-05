/-
# Mobius Root Sum 4
Category: Pure Mathematics
Target: Math.mobius_root_sum_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Math

/-- `Complex.I` is a primitive 4-th root of unity. -/
theorem isPrimitiveRoot_I : IsPrimitiveRoot Complex.I 4 := by
  refine IsPrimitiveRoot.mk_of_lt _ (by norm_num) (by simp [Complex.I_pow_four]) ?_
  intro l hl hlt
  interval_cases l <;> norm_num [pow_succ, Complex.ext_iff]

/-- `-Complex.I` is a primitive 4-th root of unity. -/
theorem isPrimitiveRoot_neg_I : IsPrimitiveRoot (-Complex.I) 4 := by
  have := isPrimitiveRoot_I.pow_of_coprime 3 (by decide)
  simpa [pow_succ, Complex.I_mul_I] using this

/-- The set of primitive 4-th roots of unity in `ℂ` is `{i, -i}`. -/
theorem primitiveRoots_four : primitiveRoots 4 ℂ = {Complex.I, -Complex.I} := by
  refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
  · intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact (mem_primitiveRoots (by norm_num)).2 isPrimitiveRoot_I
    · exact (mem_primitiveRoots (by norm_num)).2 isPrimitiveRoot_neg_I
  · rw [Complex.card_primitiveRoots,
      Finset.card_insert_of_notMem (by simp [Complex.ext_iff]; norm_num),
      Finset.card_singleton]
    decide

/-- The sum of the primitive 4-th roots of unity equals `μ(4)`. -/
theorem mobius_root_sum_4 :
    ∑ z ∈ primitiveRoots 4 ℂ, z = (ArithmeticFunction.moebius 4 : ℂ) := by
  rw [primitiveRoots_four, Finset.sum_insert (by simp [Complex.ext_iff]; norm_num),
    ArithmeticFunction.moebius_eq_zero_of_not_squarefree (by decide)]
  simp

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

