/-
# Mobius Root Sum 3
Category: Pure Mathematics
Target: Math.mobius_root_sum_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Math

open Finset ArithmeticFunction ArithmeticFunction.Moebius

/-- `ζ = exp (2 π i / 3)` is a primitive cube root of unity. -/

theorem exp_three_ne_sq :
    Complex.exp (2 * Real.pi * Complex.I / 3) ≠
      Complex.exp (2 * Real.pi * Complex.I / 3) ^ 2 := by
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / 3) with hζdef
  have hζ : IsPrimitiveRoot ζ 3 := isPrimitiveRoot_exp_three
  intro h
  have hz : ζ ≠ 0 := hζ.ne_zero (by norm_num)
  have h1 : ζ = 1 := by
    have hmul : ζ * 1 = ζ * ζ := by rw [mul_one, ← pow_two, ← h]
    exact (mul_left_cancel₀ hz hmul).symm
  rw [h1] at hζ
  have h31 : (3 : ℕ) = 1 := hζ.unique IsPrimitiveRoot.one
  omega

/-- The set of primitive cube roots of unity in `ℂ` is `{ζ, ζ²}` for
`ζ = exp (2 π i / 3)`. -/
