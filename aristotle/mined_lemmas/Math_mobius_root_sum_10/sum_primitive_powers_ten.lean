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

open Finset

namespace Math

/-- The set of primitive `10`-th roots of unity in `ℂ` is `{ζ, ζ³, ζ⁷, ζ⁹}` for any
primitive `10`-th root of unity `ζ`. -/

theorem sum_primitive_powers_ten {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 10) :
    ζ ^ 1 + ζ ^ 3 + ζ ^ 7 + ζ ^ 9 = 1 := by
  have h10 : ζ ^ 10 = 1 := hζ.pow_eq_one
  have h5 : ζ ^ 5 ≠ 1 := hζ.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
  have h2 : ζ ^ 2 ≠ 1 := hζ.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
  have h5' : ζ ^ 5 = -1 := by
    have hfac : (ζ ^ 5 - 1) * (ζ ^ 5 + 1) = 0 := by linear_combination h10
    rcases mul_eq_zero.1 hfac with h | h
    · exact absurd (by linear_combination h) h5
    · linear_combination h
  have hne : ζ + 1 ≠ 0 := fun h => h2 (by linear_combination (ζ - 1) * h)
  have key : ζ ^ 4 - ζ ^ 3 + ζ ^ 2 - ζ + 1 = 0 := by
    have hfac : (ζ + 1) * (ζ ^ 4 - ζ ^ 3 + ζ ^ 2 - ζ + 1) = 0 := by linear_combination h5'
    exact (mul_eq_zero.1 hfac).resolve_left hne
  linear_combination (ζ ^ 2 + ζ ^ 4) * h5' - key

/-- The Möbius function at `10` equals `1`. -/
