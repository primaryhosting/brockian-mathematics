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

namespace Math

/-- `Complex.I` is a primitive 4-th root of unity. -/
theorem isPrimitiveRoot_I : IsPrimitiveRoot Complex.I 4 := by
  apply IsPrimitiveRoot.mk_of_lt _ (by norm_num)
  · simp [pow_succ, Complex.I_mul_I]
  · intro l hl hl4
    interval_cases l <;> simp [pow_succ, Complex.I_mul_I] <;> norm_num [Complex.ext_iff]

/-- `-Complex.I` is a primitive 4-th root of unity. -/
theorem isPrimitiveRoot_neg_I : IsPrimitiveRoot (-Complex.I) 4 := by
  apply IsPrimitiveRoot.mk_of_lt _ (by norm_num)
  · simp [pow_succ, Complex.I_mul_I]
  · intro l hl hl4
    interval_cases l <;> simp [pow_succ, Complex.I_mul_I] <;> norm_num [Complex.ext_iff]

/-- The primitive 4-th roots of unity in `ℂ` are exactly `i` and `-i`. -/
theorem primitiveRoots_four_complex : primitiveRoots 4 ℂ = {Complex.I, -Complex.I} := by
  ext z
  simp only [Finset.mem_insert, Finset.mem_singleton,
    mem_primitiveRoots (show 0 < 4 by norm_num)]
  constructor
  · intro h
    have h4 : z ^ 4 = 1 := h.pow_eq_one
    have h2 : z ^ 2 ≠ 1 := fun hc => by
      have := h.dvd_of_pow_eq_one 2 hc
      norm_num at this
    have key : (z ^ 2 - 1) * (z ^ 2 + 1) = 0 := by linear_combination h4
    rcases mul_eq_zero.1 key with h' | h'
    · exact absurd (sub_eq_zero.1 h') h2
    · have h3 : (z - Complex.I) * (z + Complex.I) = 0 := by
        linear_combination h' - Complex.I_sq
      rcases mul_eq_zero.1 h3 with h'' | h''
      · left; linear_combination h''
      · right; linear_combination h''
  · rintro (rfl | rfl)
    · exact isPrimitiveRoot_I
    · exact isPrimitiveRoot_neg_I

/-- The sum of the primitive 4-th roots of unity equals the Möbius function at `4`. -/
theorem mobius_root_sum_4 :
    ∑ z ∈ primitiveRoots 4 ℂ, z = (ArithmeticFunction.moebius 4 : ℂ) := by
  have hne : Complex.I ≠ -Complex.I := by
    norm_num [Complex.ext_iff]
  have hmu : ArithmeticFunction.moebius 4 = 0 := by
    apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
    decide
  rw [primitiveRoots_four_complex, Finset.sum_pair hne, hmu]
  push_cast
  ring

end Math
#print axioms Math.mobius_root_sum_4

