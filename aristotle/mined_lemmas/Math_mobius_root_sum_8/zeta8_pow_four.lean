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

/-- A fixed primitive `8`-th root of unity in `ℂ`. -/

theorem zeta8_pow_four : zeta8 ^ 4 = -1 := by
  have h8 : (zeta8 ^ 4) ^ 2 = 1 := by
    rw [← pow_mul]; exact isPrimitiveRoot_zeta8.pow_eq_one
  have h : (zeta8 ^ 4 - 1) * (zeta8 ^ 4 + 1) = 0 := by linear_combination h8
  rcases mul_eq_zero.mp h with h' | h'
  · exact absurd (by linear_combination h' : zeta8 ^ 4 = 1)
      (isPrimitiveRoot_zeta8.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num))
  · linear_combination h'

/-- The sum of the primitive `8`-th roots of unity in `ℂ` equals `μ(8) = 0`. -/
