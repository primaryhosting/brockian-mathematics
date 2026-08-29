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


open scoped ArithmeticFunction.Moebius

namespace Math

/-- The set of primitive `6`-th roots of unity in `ℂ` is `{ζ, ζ ^ 5}` for any
primitive sixth root of unity `ζ`. -/

lemma sq_sub_self_add_one_eq_zero (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 6) :
    ζ ^ 2 - ζ + 1 = 0 := by
  have h6 : ζ ^ 6 = 1 := hζ.pow_eq_one
  have h3 : ζ ^ 3 ≠ 1 := hζ.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
  have h1 : ζ ^ 3 = -1 := by
    have hfac : (ζ ^ 3 - 1) * (ζ ^ 3 + 1) = 0 := by linear_combination h6
    rcases mul_eq_zero.1 hfac with h | h
    · exact absurd (sub_eq_zero.1 h) h3
    · exact eq_neg_of_add_eq_zero_left h
  have h2 : ζ ^ 2 ≠ 1 := hζ.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
  have hm1 : ζ ≠ -1 := by
    intro h
    exact h2 (by rw [h]; norm_num)
  have hfac : (ζ + 1) * (ζ ^ 2 - ζ + 1) = 0 := by linear_combination h1
  rcases mul_eq_zero.1 hfac with h | h
  · exact absurd (eq_neg_of_add_eq_zero_left h) hm1
  · exact h

/-- The sum of the primitive `6`-th roots of unity equals `μ(6) = 1`. -/
