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

lemma zeta6_pow_three : zeta6 ^ 3 = -1 := by
  have h6 : zeta6 ^ 6 = 1 := isPrimitiveRoot_zeta6.pow_eq_one
  have hne : zeta6 ^ 3 ≠ 1 :=
    isPrimitiveRoot_zeta6.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
  have hfac : (zeta6 ^ 3 - 1) * (zeta6 ^ 3 + 1) = 0 := by linear_combination h6
  rcases mul_eq_zero.1 hfac with h | h
  · exact absurd (by linear_combination h : zeta6 ^ 3 = 1) hne
  · linear_combination h

