import Mathlib

/-!
# Mobius Root Sum 6
Category: Pure Mathematics
Target: Math.mobius_root_sum_6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset Complex

namespace Math

/-- A fixed primitive 6-th root of unity in `ℂ`. -/

lemma zeta6_sq_sub : zeta6 ^ 2 - zeta6 + 1 = 0 := by
  have hne : zeta6 ≠ -1 := by
    intro h
    exact isPrimitiveRoot_zeta6.pow_ne_one_of_pos_of_lt (l := 2) (by norm_num) (by norm_num)
      (by rw [h]; norm_num)
  have hfac : (zeta6 + 1) * (zeta6 ^ 2 - zeta6 + 1) = 0 := by
    linear_combination zeta6_pow_three
  rcases mul_eq_zero.1 hfac with h | h
  · exact absurd (by linear_combination h : zeta6 = -1) hne
  · exact h

/-- The primitive 6-th roots of unity in `ℂ` are exactly `ζ` and `ζ⁵`. -/
