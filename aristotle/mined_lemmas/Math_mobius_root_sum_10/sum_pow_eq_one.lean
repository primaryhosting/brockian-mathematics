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

lemma sum_pow_eq_one {ζ : ℂ} (h : IsPrimitiveRoot ζ 10) :
    ζ ^ 1 + ζ ^ 3 + ζ ^ 7 + ζ ^ 9 = 1 := by
  have h5 : ζ ^ 5 = -1 := pow_five_eq_neg_one h
  have hc := cyclotomic_ten_eq_zero h
  have h7 : ζ ^ 7 = -ζ ^ 2 := by
    have : ζ ^ 7 = ζ ^ 5 * ζ ^ 2 := by ring
    rw [this, h5]; ring
  have h9 : ζ ^ 9 = -ζ ^ 4 := by
    have : ζ ^ 9 = ζ ^ 5 * ζ ^ 4 := by ring
    rw [this, h5]; ring
  rw [h7, h9]
  linear_combination -hc

/-- The sum of the primitive `10`-th roots of unity in `ℂ` equals `μ(10)`. -/
