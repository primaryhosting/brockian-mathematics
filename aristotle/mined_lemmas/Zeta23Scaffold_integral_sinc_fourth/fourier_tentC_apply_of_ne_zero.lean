import Mathlib

/-!
# Integral Sinc Fourth
Category: C Integral
Target: Zeta23Scaffold.integral_sinc_fourth
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Real Complex
open scoped FourierTransform

namespace Zeta23Scaffold

/-- Explicit antiderivative computation: the interval integral of a linear function times a
complex exponential. -/

lemma fourier_tentC_apply_of_ne_zero (ξ : ℝ) (hξ : ξ ≠ 0) : 𝓕 tentC ξ = sincSqC ξ := by
  set c : ℂ := -2 * (π : ℂ) * (ξ : ℂ) * I with hcdef
  have hcne : c ≠ 0 := by
    rw [hcdef]
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) ?_) ?_) Complex.I_ne_zero
    · exact_mod_cast Real.pi_ne_zero
    · exact_mod_cast hξ
  have hred : 𝓕 tentC ξ = ∫ t in (-1 : ℝ)..1, Complex.exp (c * t) * tentC t := by
    rw [Real.fourier_real_eq_integral_exp_smul]
    have hsupp : ∀ t : ℝ, t ∉ Set.Icc (-1 : ℝ) 1 →
        Complex.exp ((-2 * π * t * ξ : ℝ) * I) • tentC t = 0 := by
      intro t ht
      simp [tentC_eq_zero_of_notMem ht]
    rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hsupp,
      intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
      ← MeasureTheory.integral_Icc_eq_integral_Ioc]
    refine setIntegral_congr_fun measurableSet_Icc (fun t _ => ?_)
    rw [smul_eq_mul]
    congr 2
    rw [hcdef]
    push_cast
    ring
  rw [hred]
  have hsplit : (∫ t in (-1 : ℝ)..1, Complex.exp (c * t) * tentC t)
      = (∫ t in (-1 : ℝ)..0, Complex.exp (c * t) * tentC t)
        + (∫ t in (0 : ℝ)..1, Complex.exp (c * t) * tentC t) := by
    rw [intervalIntegral.integral_add_adjacent_intervals] <;>
      exact Continuous.intervalIntegrable (by fun_prop) _ _
  have h1 : (∫ t in (-1 : ℝ)..0, Complex.exp (c * t) * tentC t)
      = ∫ t in (-1 : ℝ)..0, (1 + 1 * (t : ℂ)) * Complex.exp (c * t) := by
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 0)] at ht
    have h : max 0 (1 - |t|) = 1 + t := by
      rw [abs_of_nonpos ht.2, max_eq_right (by linarith [ht.1])]; ring
    simp [tentC, h]
    ring
  have h2 : (∫ t in (0 : ℝ)..1, Complex.exp (c * t) * tentC t)
      = ∫ t in (0 : ℝ)..1, (1 + (-1) * (t : ℂ)) * Complex.exp (c * t) := by
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    have h : max 0 (1 - |t|) = 1 - t := by
      rw [abs_of_nonneg ht.1, max_eq_right (by linarith [ht.2])]
    simp [tentC, h]
    ring
  rw [hsplit, h1, h2, integral_lin_mul_cexp _ _ _ _ _ hcne, integral_lin_mul_cexp _ _ _ _ _ hcne]
  have hcollect :
      ((((1 : ℂ) + 1 * (((0 : ℝ)) : ℂ)) / c - 1 / c ^ 2) * cexp (c * ((0 : ℝ) : ℂ))
        - ((1 + 1 * (((-1 : ℝ)) : ℂ)) / c - 1 / c ^ 2) * cexp (c * (((-1 : ℝ)) : ℂ)))
      + ((((1 : ℂ) + (-1) * (((1 : ℝ)) : ℂ)) / c - (-1) / c ^ 2) * cexp (c * (((1 : ℝ)) : ℂ))
        - ((1 + (-1) * (((0 : ℝ)) : ℂ)) / c - (-1) / c ^ 2) * cexp (c * (((0 : ℝ)) : ℂ)))
      = (cexp c + cexp (-c) - 2) / c ^ 2 := by
    push_cast
    simp only [mul_zero, Complex.exp_zero, mul_one, mul_neg]
    field_simp
    ring
  rw [hcollect]
  have hz : (-c) = ((2 * π * ξ : ℝ) : ℂ) * I := by rw [hcdef]; push_cast; ring
  have hz2 : c = -(((2 * π * ξ : ℝ) : ℂ)) * I := by rw [hcdef]; push_cast; ring
  have hcos : Complex.exp c + Complex.exp (-c) = 2 * Complex.cos ((2 * π * ξ : ℝ) : ℂ) := by
    rw [Complex.cos, hz, hz2]; ring
  have hcr : Complex.cos ((2 * π * ξ : ℝ) : ℂ) = ((Real.cos (2 * π * ξ) : ℝ) : ℂ) :=
    (Complex.ofReal_cos _).symm
  have hcd : Real.cos (2 * π * ξ) = 1 - 2 * Real.sin (π * ξ) ^ 2 := by
    have h : (2 : ℝ) * π * ξ = 2 * (π * ξ) := by ring
    rw [h, Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq (π * ξ)]
  have hc2 : c ^ 2 = -(4 * (π : ℂ) ^ 2 * (ξ : ℂ) ^ 2) := by
    rw [hcdef]; ring_nf; rw [Complex.I_sq]; ring
  have hpx : (π : ℂ) * (ξ : ℂ) ≠ 0 := by
    refine mul_ne_zero ?_ ?_
    · exact_mod_cast Real.pi_ne_zero
    · exact_mod_cast hξ
  have hsinc : sincSqC ξ = ((Real.sin (π * ξ) / (π * ξ)) ^ 2 : ℝ) := by
    rw [sincSqC, Real.sinc_of_ne_zero (mul_ne_zero Real.pi_ne_zero hξ)]
  rw [hcos, hcr, hcd, hc2, hsinc]
  push_cast
  field_simp
  ring

