/-
# Mobius Root Sum 8
Category: Pure Mathematics
Target: Math.mobius_root_sum_8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators

namespace Math

/-- A primitive `8`-th root of unity satisfies `ζ ^ 4 = -1`. -/

lemma pow_four_eq_neg_one_of_isPrimitiveRoot_eight {z : ℂ} (hz : IsPrimitiveRoot z 8) :
    z ^ 4 = -1 := by
  have h8 : (z ^ 4) ^ 2 = 1 := by
    rw [← pow_mul]; simpa using hz.pow_eq_one
  have h4 : z ^ 4 ≠ 1 := hz.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
  have h8' : z ^ 4 * z ^ 4 = 1 := by rw [← sq]; exact h8
  rcases mul_self_eq_one_iff.1 h8' with h | h
  · exact absurd h h4
  · exact h

/-- Negation maps primitive `8`-th roots of unity to primitive `8`-th roots of unity. -/
