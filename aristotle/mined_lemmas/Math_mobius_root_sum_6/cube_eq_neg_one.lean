/-
# Mobius Root Sum 6
Category: Pure Mathematics
Target: Math.mobius_root_sum_6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Mobius Root Sum 6
Category: Pure Mathematics
Target: Math.mobius_root_sum_6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Complex Finset

namespace Math

/-- A primitive 6-th root of unity `ζ` satisfies `ζ ^ 3 = -1`. -/

lemma cube_eq_neg_one {ζ : ℂ} (h : IsPrimitiveRoot ζ 6) : ζ ^ 3 = -1 := by
  have h6 : ζ ^ 6 = 1 := h.pow_eq_one
  have h3 : ζ ^ 3 ≠ 1 := h.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
  have hsq : (ζ ^ 3) ^ 2 = 1 := by
    rw [← pow_mul]; simpa using h6
  rcases mul_self_eq_one_iff.1 (by linear_combination hsq : ζ ^ 3 * ζ ^ 3 = 1) with h' | h'
  · exact absurd h' h3
  · exact h'

/-- A primitive 6-th root of unity `ζ` satisfies `ζ ^ 2 - ζ + 1 = 0`. -/
