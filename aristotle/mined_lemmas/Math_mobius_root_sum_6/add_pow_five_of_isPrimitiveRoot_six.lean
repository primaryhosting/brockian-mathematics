/-
# Mobius Root Sum 6
Category: Pure Mathematics
Target: Math.mobius_root_sum_6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Finset

namespace Math

/-- The Möbius function at `6` equals `1`. -/

theorem add_pow_five_of_isPrimitiveRoot_six {ζ : ℂ} (h : IsPrimitiveRoot ζ 6) :
    ζ + ζ ^ 5 = 1 := by
  have h6 : ζ ^ 6 = 1 := h.pow_eq_one
  have h3 : ζ ^ 3 = -1 := by
    have h1 : ζ ^ 3 ≠ 1 := h.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
    have hfac : (ζ ^ 3 - 1) * (ζ ^ 3 + 1) = 0 := by linear_combination h6
    rcases mul_eq_zero.1 hfac with hc | hc
    · exact absurd (by linear_combination hc) h1
    · linear_combination hc
  have h2 : ζ ≠ -1 := by
    intro he
    exact h.pow_ne_one_of_pos_of_lt (l := 2) (by norm_num) (by norm_num) (by rw [he]; ring)
  have key : ζ ^ 2 - ζ + 1 = 0 := by
    have hfac : (ζ + 1) * (ζ ^ 2 - ζ + 1) = 0 := by linear_combination h3
    rcases mul_eq_zero.1 hfac with hc | hc
    · exact absurd (by linear_combination hc) h2
    · exact hc
  linear_combination -key + ζ ^ 2 * h3

/-- The sum of the primitive `6`-th roots of unity in `ℂ` equals `μ 6`. -/
