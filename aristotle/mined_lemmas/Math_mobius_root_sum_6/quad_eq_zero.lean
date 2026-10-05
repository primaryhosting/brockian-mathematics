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

open Complex Finset

namespace Math

/-- A primitive 6-th root of unity `ζ` satisfies `ζ ^ 3 = -1`. -/

lemma quad_eq_zero {ζ : ℂ} (h : IsPrimitiveRoot ζ 6) : ζ ^ 2 - ζ + 1 = 0 := by
  have h3 : ζ ^ 3 = -1 := cube_eq_neg_one h
  have hne : ζ + 1 ≠ 0 := by
    intro hc
    have hz : ζ = -1 := by linear_combination hc
    have h2 : ζ ^ 2 ≠ 1 := h.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
    exact h2 (by rw [hz]; ring)
  have hfac : (ζ + 1) * (ζ ^ 2 - ζ + 1) = 0 := by linear_combination h3
  rcases mul_eq_zero.1 hfac with h' | h'
  · exact absurd h' hne
  · exact h'

/-- `μ(6) = 1`. -/
