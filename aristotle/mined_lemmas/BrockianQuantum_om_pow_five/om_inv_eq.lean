import Mathlib
/-!
# Batch 7 — fifth roots of unity ω = exp(2πi/5): the Brockian-five / QFT-on-ℤ5 core. All TRUE.
-/
namespace BrockianQuantum
open Complex

theorem om_inv_eq : om⁻¹ = om ^ 4 := by
  have h4 : om ^ 4 * om = 1 := by linear_combination om_pow_five
  exact (eq_inv_of_mul_eq_one_left h4).symm

