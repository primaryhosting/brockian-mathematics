/-
# Mobius Root Sum 10
Category: Pure Mathematics
Target: Math.mobius_root_sum_10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Finset

namespace Math

/-- The Möbius function at `10` equals `1`. -/

lemma cyclotomic_ten_eq_zero {ζ : ℂ} (h : IsPrimitiveRoot ζ 10) :
    ζ ^ 4 - ζ ^ 3 + ζ ^ 2 - ζ + 1 = 0 := by
  have h5 : ζ ^ 5 = -1 := pow_five_eq_neg_one h
  have hne : ζ + 1 ≠ 0 := by
    intro hz
    have hζ : ζ = -1 := by linear_combination hz
    have h2 : ζ ^ 2 = 1 := by rw [hζ]; norm_num
    exact h.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num) h2
  have hprod : (ζ + 1) * (ζ ^ 4 - ζ ^ 3 + ζ ^ 2 - ζ + 1) = 0 := by
    linear_combination h5
  rcases mul_eq_zero.mp hprod with h1 | h1
  · exact absurd h1 hne
  · exact h1

/-- The sum of the four primitive `10`-th roots of unity, expressed via a fixed primitive root. -/
