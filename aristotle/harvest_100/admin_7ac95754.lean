/-
# Mobius Root Sum 4
Category: Pure Mathematics
Target: Math.mobius_root_sum_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators

namespace Math

/-- `Complex.I` is a primitive `4`-th root of unity. -/
lemma isPrimitiveRoot_I : IsPrimitiveRoot Complex.I 4 := by
  refine IsPrimitiveRoot.mk_of_lt _ (by norm_num) (by simp [pow_succ, Complex.I_mul_I]) ?_
  intro l hl hlt
  interval_cases l <;> simp [pow_succ, Complex.I_mul_I] <;> norm_num [Complex.ext_iff]

/-- `-Complex.I` is a primitive `4`-th root of unity. -/
lemma isPrimitiveRoot_neg_I : IsPrimitiveRoot (-Complex.I) 4 := by
  refine IsPrimitiveRoot.mk_of_lt _ (by norm_num) (by simp [pow_succ, Complex.I_mul_I]) ?_
  intro l hl hlt
  interval_cases l <;> simp [pow_succ, Complex.I_mul_I] <;> norm_num [Complex.ext_iff]

/-- A complex number is a primitive `4`-th root of unity iff it is `I` or `-I`. -/
lemma isPrimitiveRoot_four_iff (z : ℂ) :
    IsPrimitiveRoot z 4 ↔ z = Complex.I ∨ z = -Complex.I := by
  constructor
  · intro h
    have h4 : z ^ 4 = 1 := h.pow_eq_one
    have h2 : z ^ 2 ≠ 1 := h.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
    have hsq : z ^ 2 = -1 := by
      have : (z ^ 2 - 1) * (z ^ 2 + 1) = 0 := by ring_nf; linear_combination h4
      rcases mul_eq_zero.mp this with h' | h'
      · exact absurd (by linear_combination h') h2
      · linear_combination h'
    have : (z - Complex.I) * (z + Complex.I) = 0 := by
      have hI : Complex.I ^ 2 = -1 := Complex.I_sq
      linear_combination hsq - hI
    rcases mul_eq_zero.mp this with h' | h'
    · left; linear_combination h'
    · right; linear_combination h'
  · rintro (rfl | rfl)
    · exact isPrimitiveRoot_I
    · exact isPrimitiveRoot_neg_I

/-- The set of primitive `4`-th roots of unity in `ℂ` is `{I, -I}`. -/
lemma primitiveRoots_four : primitiveRoots 4 ℂ = {Complex.I, -Complex.I} := by
  ext z
  simp only [mem_primitiveRoots (show 0 < 4 by norm_num), Finset.mem_insert,
    Finset.mem_singleton]
  exact isPrimitiveRoot_four_iff z

/-- The sum of the primitive `4`-th roots of unity equals `μ(4)`. -/
theorem mobius_root_sum_4 :
    ∑ z ∈ primitiveRoots 4 ℂ, z = (ArithmeticFunction.moebius 4 : ℂ) := by
  have h4 : ArithmeticFunction.moebius 4 = 0 := by decide
  rw [primitiveRoots_four, h4]
  rw [Finset.sum_pair (by norm_num [Complex.ext_iff])]
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

