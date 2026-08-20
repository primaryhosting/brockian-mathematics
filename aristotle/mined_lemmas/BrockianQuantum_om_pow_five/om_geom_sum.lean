import Mathlib
/-!
# Batch 7 — fifth roots of unity ω = exp(2πi/5): the Brockian-five / QFT-on-ℤ5 core. All TRUE.
-/
namespace BrockianQuantum
open Complex

theorem om_geom_sum : 1 + om + om ^ 2 + om ^ 3 + om ^ 4 = 0 := by
  have hsub : om - 1 ≠ 0 := sub_ne_zero.mpr om_ne_one
  have h : (om - 1) * (1 + om + om ^ 2 + om ^ 3 + om ^ 4) = 0 := by
    linear_combination om_pow_five
  rcases mul_eq_zero.mp h with h' | h'
  · exact absurd h' hsub
  · exact h'
end BrockianQuantum

