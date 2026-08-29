import Mathlib

/-!
# Mobius Root Sum 12
Category: Pure Mathematics
Target: Math.mobius_root_sum_12
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace Math

/-- If `z` is a primitive `12`-th root of unity in `ℂ`, then `z ^ 6 = -1`. -/

lemma pow_six_eq_neg_one {z : ℂ} (hz : IsPrimitiveRoot z 12) : z ^ 6 = -1 := by
  have h12 : (z ^ 6) ^ 2 = 1 := by
    rw [← pow_mul]; exact hz.pow_eq_one
  have hne : z ^ 6 ≠ 1 := hz.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
  have hfac : (z ^ 6 - 1) * (z ^ 6 + 1) = 0 := by linear_combination h12
  rcases mul_eq_zero.mp hfac with h | h
  · exact absurd (by linear_combination h) hne
  · linear_combination h

/-- Negation maps primitive `12`-th roots of unity to primitive `12`-th roots of unity. -/
