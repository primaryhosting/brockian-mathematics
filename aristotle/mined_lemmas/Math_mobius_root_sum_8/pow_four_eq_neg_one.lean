import Mathlib

/-!
# Mobius Root Sum 8
Category: Pure Mathematics
Target: Math.mobius_root_sum_8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace Math

/-- A primitive 8-th root of unity satisfies `z ^ 4 = -1`. -/

lemma pow_four_eq_neg_one {z : ℂ} (hz : IsPrimitiveRoot z 8) : z ^ 4 = -1 := by
  have h8 : z ^ 8 = 1 := hz.pow_eq_one
  have h4 : z ^ 4 ≠ 1 := hz.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
  have hfac : (z ^ 4 - 1) * (z ^ 4 + 1) = 0 := by linear_combination h8
  rcases mul_eq_zero.1 hfac with h | h
  · exact absurd (sub_eq_zero.1 h) h4
  · linear_combination h

/-- For a primitive 8-th root of unity, `z ^ 5 = -z`. -/
