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

theorem primitiveRoots_four_complex : primitiveRoots 4 ℂ = {Complex.I, -Complex.I} := by
  ext z
  rw [mem_primitiveRoots (by norm_num)]
  constructor
  · intro h
    have h4 : z ^ 4 = 1 := h.pow_eq_one
    have h2 : z ^ 2 ≠ 1 := by
      intro h2
      have : (4 : ℕ) ∣ 2 := h.dvd_of_pow_eq_one 2 h2
      omega
    have key : (z ^ 2 - 1) * (z ^ 2 + 1) = 0 := by linear_combination h4
    rcases mul_eq_zero.1 key with h' | h'
    · exact absurd (by linear_combination h') h2
    · have hz : (z - Complex.I) * (z + Complex.I) = 0 := by
        linear_combination h' - Complex.I_sq
      rcases mul_eq_zero.1 hz with h'' | h''
      · simp [sub_eq_zero.1 h'']
      · simp [eq_neg_of_add_eq_zero_left h'']
  · intro h
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with rfl | rfl
    · exact I_isPrimitiveRoot_four
    · exact neg_I_isPrimitiveRoot_four

/-- The sum of the primitive 4-th roots of unity equals `μ 4`. -/
