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
