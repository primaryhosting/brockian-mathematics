/-
# Mobius Root Sum 10
Category: Pure Mathematics
Target: Math.mobius_root_sum_10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Mobius Root Sum 10
Category: Pure Mathematics
Target: Math.mobius_root_sum_10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

open ArithmeticFunction Finset

/-- The Möbius function at `10` equals `1`. -/

lemma cyclotomic_ten_eval {ζ : ℂ} (h : IsPrimitiveRoot ζ 10) :
    ζ ^ 4 - ζ ^ 3 + ζ ^ 2 - ζ + 1 = 0 := by
  have h5 : ζ ^ 5 = -1 := pow_five_eq_neg_one h
  have hne : ζ + 1 ≠ 0 := by
    intro hc
    have hsq : ζ ^ 2 = 1 := by linear_combination (ζ - 1) * hc
    exact h.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num) hsq
  have hprod : (ζ + 1) * (ζ ^ 4 - ζ ^ 3 + ζ ^ 2 - ζ + 1) = 0 := by linear_combination h5
  exact (mul_eq_zero.mp hprod).resolve_left hne

/-- Distinct exponents below `10` give distinct powers of a primitive `10`-th root of unity. -/
