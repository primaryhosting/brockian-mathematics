/-
# Mobius Root Sum 2
Category: Pure Mathematics
Target: Math.mobius_root_sum_2
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Math

/-- The only primitive `2`-nd root of unity in `ℂ` is `-1`. -/

theorem isPrimitiveRoot_two_iff (x : ℂ) : IsPrimitiveRoot x 2 ↔ x = -1 := by
  constructor
  · intro h
    have h2 : x ^ 2 = 1 := h.pow_eq_one
    have h1 : x ≠ 1 := h.ne_one one_lt_two
    have hz : (x - 1) * (x + 1) = 0 := by linear_combination h2
    rcases mul_eq_zero.1 hz with h' | h'
    · exact absurd (sub_eq_zero.1 h') h1
    · linear_combination h'
  · rintro rfl
    exact IsPrimitiveRoot.neg_one _ (by norm_num)

/-- The set of primitive `2`-nd roots of unity in `ℂ` is `{-1}`. -/
