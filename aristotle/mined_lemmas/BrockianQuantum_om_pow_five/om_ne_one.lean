import Mathlib
/-!
# Batch 7 — fifth roots of unity ω = exp(2πi/5): the Brockian-five / QFT-on-ℤ5 core. All TRUE.
-/
namespace BrockianQuantum
open Complex

theorem om_ne_one : om ≠ 1 := by
  rw [Ne, om, Complex.exp_eq_one_iff]
  push_neg
  intro n h
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hz : (2 : ℂ) * Real.pi * Complex.I ≠ 0 := by simp [hpi, Complex.I_ne_zero]
  have h2 : (2 * (Real.pi : ℂ) * Complex.I) * (1 / 5)
      = (2 * (Real.pi : ℂ) * Complex.I) * (n : ℂ) := by
    linear_combination h
  have h3 := mul_left_cancel₀ hz h2
  have h5 : (n : ℂ) * 5 = 1 := by linear_combination -5 * h3
  have h5' : (n : ℚ) * 5 = 1 := by exact_mod_cast h5
  have hn : (n : ℚ) = 1 / 5 := by linarith
  have hden : ((n : ℤ) : ℚ).den = 1 := Rat.den_intCast n
  rw [hn] at hden
  norm_num at hden

