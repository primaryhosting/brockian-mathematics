import Mathlib

/-!
# Mobius Root Sum 4
Category: Pure Mathematics
Target: Math.mobius_root_sum_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-- `Complex.I` is a primitive 4-th root of unity. -/
theorem isPrimitiveRoot_I : IsPrimitiveRoot Complex.I 4 := by
  apply IsPrimitiveRoot.mk_of_lt _ (by norm_num) (by simp [pow_succ, Complex.I_mul_I])
  intro l hl hl4
  interval_cases l <;> norm_num [pow_succ, Complex.I_mul_I, Complex.ext_iff]

/-- `-Complex.I` is a primitive 4-th root of unity. -/
theorem isPrimitiveRoot_neg_I : IsPrimitiveRoot (-Complex.I) 4 := by
  apply IsPrimitiveRoot.mk_of_lt _ (by norm_num) (by simp [pow_succ, Complex.I_mul_I])
  intro l hl hl4
  interval_cases l <;> norm_num [pow_succ, Complex.I_mul_I, Complex.ext_iff]

/-- The primitive 4-th roots of unity in `ℂ` are exactly `I` and `-I`. -/
theorem primitiveRoots_four_complex : primitiveRoots 4 ℂ = {Complex.I, -Complex.I} := by
  ext x
  rw [mem_primitiveRoots (by norm_num), Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro h
    have h4 : x ^ 4 = 1 := h.pow_eq_one
    have h2 : x ^ 2 ≠ 1 := by
      intro hh
      have := (h.pow_eq_one_iff_dvd 2).1 hh
      omega
    have key : (x ^ 2 - 1) * (x ^ 2 + 1) = 0 := by linear_combination h4
    rcases mul_eq_zero.1 key with h' | h'
    · exact absurd (by linear_combination h') h2
    · have hx2 : x ^ 2 = -1 := by linear_combination h'
      have key2 : (x - Complex.I) * (x + Complex.I) = 0 := by
        linear_combination hx2 - Complex.I_sq
      rcases mul_eq_zero.1 key2 with h'' | h''
      · exact Or.inl (sub_eq_zero.1 h'')
      · exact Or.inr (eq_neg_of_add_eq_zero_left h'')
  · rintro (rfl | rfl)
    · exact isPrimitiveRoot_I
    · exact isPrimitiveRoot_neg_I

/-- The sum of the primitive 4-th roots of unity equals `μ(4)`. -/
theorem mobius_root_sum_4 :
    ∑ z ∈ primitiveRoots 4 ℂ, z = (ArithmeticFunction.moebius 4 : ℂ) := by
  rw [primitiveRoots_four_complex]
  rw [Finset.sum_insert (by norm_num [Complex.ext_iff]), Finset.sum_singleton]
  have : ArithmeticFunction.moebius 4 = 0 := by decide
  simp [this]

end Math

