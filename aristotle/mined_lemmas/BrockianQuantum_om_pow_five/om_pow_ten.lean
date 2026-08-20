import Mathlib
/-!
# Batch 7 — fifth roots of unity ω = exp(2πi/5): the Brockian-five / QFT-on-ℤ5 core. All TRUE.
-/
namespace BrockianQuantum
open Complex

theorem om_pow_ten : om ^ 10 = 1 := by
  rw [show (10 : ℕ) = 5 * 2 from rfl, pow_mul, om_pow_five, one_pow]

