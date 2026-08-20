import Mathlib
/-!
# Batch 7 — fifth roots of unity ω = exp(2πi/5): the Brockian-five / QFT-on-ℤ5 core. All TRUE.
-/
namespace BrockianQuantum
open Complex

theorem om_pow_five : om ^ 5 = 1 := by
  rw [om, ← Complex.exp_nat_mul,
    show ((5 : ℕ) : ℂ) * (2 * Real.pi * Complex.I / 5) = 2 * Real.pi * Complex.I by
      push_cast; ring]
  exact Complex.exp_two_pi_mul_I

