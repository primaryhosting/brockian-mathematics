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
lemma isPrimitiveRoot_I : IsPrimitiveRoot Complex.I 4 := by
  apply IsPrimitiveRoot.mk_of_lt
  · norm_num
  · norm_num
  · intro l hl hl4
    interval_cases l <;> norm_num [pow_succ, Complex.ext_iff]

/-- `-Complex.I` is a primitive 4-th root of unity. -/
lemma isPrimitiveRoot_neg_I : IsPrimitiveRoot (-Complex.I) 4 := by
  apply IsPrimitiveRoot.mk_of_lt
  · norm_num
  · norm_num
  · intro l hl hl4
    interval_cases l <;> norm_num [pow_succ, Complex.ext_iff]

/-- A complex number is a primitive 4-th root of unity iff it is `± I`. -/
lemma isPrimitiveRoot_four_iff (x : ℂ) : IsPrimitiveRoot x 4 ↔ (x = Complex.I ∨ x = -Complex.I) := by
  constructor
  · intro h
    have h4 : x ^ 4 = 1 := h.pow_eq_one
    have h2 : x ^ 2 ≠ 1 := by
      intro h2
      have := h.dvd_of_pow_eq_one 2 h2
      omega
    have hfac : (x ^ 2 - 1) * (x ^ 2 + 1) = 0 := by ring_nf; linear_combination h4
    have hsq : x ^ 2 + 1 = 0 := by
      rcases mul_eq_zero.1 hfac with h' | h'
      · exact absurd (by linear_combination h') h2
      · exact h'
    have : (x - Complex.I) * (x + Complex.I) = 0 := by
      have hI : Complex.I ^ 2 = -1 := Complex.I_sq
      linear_combination hsq - hI
    rcases mul_eq_zero.1 this with h' | h'
    · exact Or.inl (sub_eq_zero.1 h')
    · exact Or.inr (by linear_combination h')
  · rintro (rfl | rfl)
    · exact isPrimitiveRoot_I
    · exact isPrimitiveRoot_neg_I

/-- The set of primitive 4-th roots of unity in `ℂ` is `{I, -I}`. -/
lemma primitiveRoots_four : primitiveRoots 4 ℂ = {Complex.I, -Complex.I} := by
  ext x
  rw [mem_primitiveRoots (by norm_num), isPrimitiveRoot_four_iff]
  simp

/-- The sum of the primitive 4-th roots of unity equals `μ(4)`. -/
theorem mobius_root_sum_4 :
    ∑ z ∈ primitiveRoots 4 ℂ, z = (ArithmeticFunction.moebius 4 : ℤ) := by
  rw [primitiveRoots_four]
  rw [Finset.sum_insert (by simp [Complex.ext_iff]; norm_num)]
  have h4 : ArithmeticFunction.moebius 4 = 0 := by decide
  simp [h4]

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

