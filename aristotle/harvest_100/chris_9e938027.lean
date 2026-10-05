/-
# Mobius Root Sum 4
Category: Pure Mathematics
Target: Math.mobius_root_sum_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Mobius Root Sum 4
Category: Pure Mathematics
Target: Math.mobius_root_sum_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


namespace Math

open Finset Complex

/-- `Complex.I` is a primitive 4-th root of unity. -/
theorem isPrimitiveRoot_I : IsPrimitiveRoot Complex.I 4 := by
  refine IsPrimitiveRoot.mk_of_lt _ (by norm_num) (by simp [pow_succ, Complex.I_mul_I]) ?_
  intro l hl hlt
  interval_cases l <;>
    norm_num [pow_succ, Complex.I_mul_I, Complex.ext_iff]

/-- `-Complex.I` is a primitive 4-th root of unity. -/
theorem isPrimitiveRoot_neg_I : IsPrimitiveRoot (-Complex.I) 4 := by
  refine IsPrimitiveRoot.mk_of_lt _ (by norm_num) (by simp [pow_succ, Complex.I_mul_I]) ?_
  intro l hl hlt
  interval_cases l <;>
    norm_num [pow_succ, Complex.I_mul_I, Complex.ext_iff]

/-- The primitive 4-th roots of unity in `ℂ` are exactly `I` and `-I`. -/
theorem primitiveRoots_four_eq : primitiveRoots 4 ℂ = {Complex.I, -Complex.I} := by
  ext z
  rw [mem_primitiveRoots (by norm_num)]
  constructor
  · intro hz
    have h4 : z ^ 4 = 1 := hz.pow_eq_one
    have h2 : z ^ 2 ≠ 1 := fun h => by
      have := hz.dvd_of_pow_eq_one 2 h
      omega
    have : (z ^ 2 - 1) * (z - Complex.I) * (z + Complex.I) = 0 := by
      have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
      linear_combination h4 - (z ^ 2 - 1) * hI
    rcases mul_eq_zero.mp this with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact absurd (by linear_combination h) h2
      · simp [Finset.mem_insert, sub_eq_zero.mp h]
    · have : z = -Complex.I := by linear_combination h
      simp [this]
  · intro hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact isPrimitiveRoot_I
    · exact isPrimitiveRoot_neg_I

/-- The sum of the primitive 4-th roots of unity equals `μ(4) = 0`. -/
theorem mobius_root_sum_4 :
    ∑ z ∈ primitiveRoots 4 ℂ, z = (ArithmeticFunction.moebius 4 : ℂ) := by
  rw [primitiveRoots_four_eq]
  rw [Finset.sum_insert (by norm_num [Complex.ext_iff]), Finset.sum_singleton]
  have : ArithmeticFunction.moebius 4 = 0 := by decide
  simp [this]

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

