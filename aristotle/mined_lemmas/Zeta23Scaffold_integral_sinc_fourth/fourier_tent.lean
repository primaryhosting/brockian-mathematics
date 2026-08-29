import Mathlib

/-!
# Integral Sinc Fourth
Category: C Integral
Target: Zeta23Scaffold.integral_sinc_fourth
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Zeta23Scaffold

open MeasureTheory Real FourierTransform Complex intervalIntegral

/-- The tent (triangle) function `max 0 (1 - |x|)`, viewed as a complex-valued function. -/

lemma fourier_tent (ξ : ℝ) : 𝓕 tent ξ = ((Real.sinc (π * ξ) ^ 2 : ℝ) : ℂ) := by
  rcases eq_or_ne ξ 0 with rfl | hξ
  · rw [Real.fourier_real_eq]
    simp only [mul_zero, neg_zero, AddChar.map_zero_eq_one, one_smul]
    have h2 : ∫ v : ℝ, tent v = ((∫ v : ℝ, (max 0 (1 - |v|)) : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      rfl
    have h1 := integral_tent_pow 1 one_ne_zero
    simp only [pow_one, Nat.cast_one] at h1
    rw [h2, h1]
    norm_num
  · set c : ℂ := 2 * π * ξ * I with hcdef
    have hne : ((2 * π * ξ : ℝ) : ℂ) ≠ 0 := by
      simp only [ne_eq, Complex.ofReal_eq_zero]
      positivity
    have hz : c = ((2 * π * ξ : ℝ) : ℂ) * I := by rw [hcdef]; push_cast; ring
    have hc : c ≠ 0 := by
      rw [hz]
      exact mul_ne_zero hne Complex.I_ne_zero
    rw [fourier_tent_eq_intervalIntegral ξ,
      ← intervalIntegral.integral_add_adjacent_intervals (b := (0 : ℝ)) (a := -1) (c := 1)
        (Continuous.intervalIntegrable (by unfold tent; fun_prop) _ _)
        (Continuous.intervalIntegrable (by unfold tent; fun_prop) _ _)]
    have e1 : (∫ v in (-1 : ℝ)..0, Complex.exp (-(c * v)) * tent v)
        = ∫ v in (-1 : ℝ)..0, Complex.exp (-(c * v)) * (1 + v) := by
      apply intervalIntegral.integral_congr
      intro v hv
      simp only [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 0), Set.mem_Icc] at hv
      dsimp only
      rw [show tent v = ((1 + v : ℝ) : ℂ) by
        simp only [tent]
        rw [abs_of_nonpos hv.2, max_eq_right (by linarith)]
        push_cast
        ring]
      push_cast
      ring
    have e2 : (∫ v in (0 : ℝ)..1, Complex.exp (-(c * v)) * tent v)
        = ∫ v in (0 : ℝ)..1, Complex.exp (-(c * v)) * (1 - v) := by
      apply intervalIntegral.integral_congr
      intro v hv
      simp only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1), Set.mem_Icc] at hv
      dsimp only
      rw [show tent v = ((1 - v : ℝ) : ℂ) by
        simp only [tent]
        rw [abs_of_nonneg hv.1, max_eq_right (by linarith)]]
      push_cast
      ring
    rw [e1, e2, tent_exp_integral c hc, hz]
    rw [Complex.exp_mul_I,
      show -(((2 * π * ξ : ℝ) : ℂ) * I) = (-((2 * π * ξ : ℝ) : ℂ)) * I by ring,
      Complex.exp_mul_I, mul_pow, Complex.I_sq]
    simp only [Complex.cos_neg, Complex.sin_neg, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    have hpx : (π * ξ) ≠ 0 := by positivity
    rw [Real.sinc_of_ne_zero hpx]
    have hcos : Real.cos (2 * π * ξ) = 1 - 2 * Real.sin (π * ξ) ^ 2 := by
      have h6 := Real.cos_two_mul (π * ξ)
      have h7 := Real.sin_sq_add_cos_sq (π * ξ)
      rw [show 2 * π * ξ = 2 * (π * ξ) by ring]
      nlinarith
    have hpc : ((π * ξ : ℝ) : ℂ) ≠ 0 := by
      simp only [ne_eq, Complex.ofReal_eq_zero]
      exact hpx
    rw [hcos]
    push_cast
    field_simp
    ring

