import Mathlib

/-!
# Mobius Root Sum 6
Category: Pure Mathematics
Target: Math.mobius_root_sum_6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace Math

/-- A primitive `6`-th root of unity `ζ` in `ℂ` satisfies `ζ ^ 3 = -1`. -/

theorem ne_pow_five_of_isPrimitiveRoot_six {ζ : ℂ} (h : IsPrimitiveRoot ζ 6) :
    ζ ≠ ζ ^ 5 := by
  intro he
  have hζ0 : ζ ≠ 0 := h.ne_zero (by norm_num)
  have h4 : ζ ^ 4 = 1 := by
    have : ζ * (ζ ^ 4 - 1) = 0 := by linear_combination -he
    rcases mul_eq_zero.1 this with h' | h'
    · exact absurd h' hζ0
    · linear_combination h'
  exact h.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num) h4

/-- The set of primitive `6`-th roots of unity in `ℂ` is `{ζ, ζ ^ 5}` for any
primitive `6`-th root of unity `ζ`. -/
