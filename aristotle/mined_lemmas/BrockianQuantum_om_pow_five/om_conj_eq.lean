import Mathlib
/-!
# Batch 7 — fifth roots of unity ω = exp(2πi/5): the Brockian-five / QFT-on-ℤ5 core. All TRUE.
-/
namespace BrockianQuantum
open Complex

theorem om_conj_eq : (starRingEnd ℂ) om = om ^ 4 := by
  rw [← Complex.inv_eq_conj om_norm_one, om_inv_eq]

