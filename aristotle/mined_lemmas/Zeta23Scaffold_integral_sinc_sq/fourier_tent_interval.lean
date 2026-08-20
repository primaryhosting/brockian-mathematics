/-
# Integral Sinc Sq
Category: C Integral
Target: Zeta23Scaffold.integral_sinc_sq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open MeasureTheory Real Complex
open scoped FourierTransform

namespace Zeta23Scaffold

/-! ### The tent function and its Fourier transform -/

/-- The triangular ("tent") function `max (1 - |x|) 0`, supported on `[-1, 1]`. -/

lemma fourier_tent_interval (ξ : ℝ) :
    𝓕 (fun x : ℝ => (tent x : ℂ)) ξ
      = ∫ x in (-1 : ℝ)..1, Complex.exp (↑(-2 * π * x * ξ) * Complex.I) • (tent x : ℂ) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  rw [intervalIntegral.integral_of_le (by norm_num), ← MeasureTheory.integral_Icc_eq_integral_Ioc,
    MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero]
  intro x hx
  simp only [Set.mem_Icc, not_and_or, not_le] at hx
  have : tent x = 0 := by
    refine tent_eq_zero ?_
    rcases hx with h | h
    · exact le_abs.2 (Or.inr (by linarith))
    · exact le_abs.2 (Or.inl (by linarith))
  simp [this]

/-- The Fourier transform of the tent function is `sinc (π ξ) ^ 2`. -/
