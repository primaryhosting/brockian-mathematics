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

theorem sq_sub_self_add_one_of_isPrimitiveRoot_six {ζ : ℂ} (h : IsPrimitiveRoot ζ 6) :
    ζ ^ 2 - ζ + 1 = 0 := by
  have h2 : ζ ^ 2 ≠ 1 := h.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
  have hcube : ζ ^ 3 = -1 := cube_eq_neg_one_of_isPrimitiveRoot_six h
  have hne : ζ + 1 ≠ 0 := by
    intro h'
    exact h2 (by linear_combination (ζ - 1) * h')
  have key : (ζ + 1) * (ζ ^ 2 - ζ + 1) = 0 := by linear_combination hcube
  rcases mul_eq_zero.1 key with h' | h'
  · exact absurd h' hne
  · exact h'

/-- A primitive `6`-th root of unity is different from its fifth power. -/
