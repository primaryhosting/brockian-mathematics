import Mathlib

/-!
# Mobius Root Sum 6
Category: Pure Mathematics
Target: Math.mobius_root_sum_6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace Math

/-- A primitive `6`-th root of unity `ζ` in `ℂ` satisfies `ζ ^ 3 = -1`. -/

theorem cube_eq_neg_one_of_isPrimitiveRoot_six {ζ : ℂ} (h : IsPrimitiveRoot ζ 6) :
    ζ ^ 3 = -1 := by
  have h6 : ζ ^ 6 = 1 := h.pow_eq_one
  have h3 : ζ ^ 3 ≠ 1 := h.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
  have key : (ζ ^ 3 - 1) * (ζ ^ 3 + 1) = 0 := by linear_combination h6
  rcases mul_eq_zero.1 key with h' | h'
  · exact absurd (by linear_combination h' : ζ ^ 3 = 1) h3
  · linear_combination h'

/-- A primitive `6`-th root of unity `ζ` in `ℂ` satisfies `ζ ^ 2 - ζ + 1 = 0`. -/
