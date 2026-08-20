/-
# Mobius Root Sum 8
Category: Pure Mathematics
Target: Math.mobius_root_sum_8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Finset

namespace Math

/-- A primitive `8`-th root of unity satisfies `z ^ 4 = -1`. -/

theorem primRoot8_pow_four {z : ℂ} (h : IsPrimitiveRoot z 8) : z ^ 4 = -1 := by
  have h8 : z ^ 8 = 1 := h.pow_eq_one
  have h4 : z ^ 4 ≠ 1 := h.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
  have hfac : (z ^ 4 - 1) * (z ^ 4 + 1) = 0 := by linear_combination h8
  rcases mul_eq_zero.1 hfac with h1 | h1
  · exact absurd (by linear_combination h1) h4
  · linear_combination h1

/-- The negation of a primitive `8`-th root of unity is again one (indeed `-z = z ^ 5`). -/
