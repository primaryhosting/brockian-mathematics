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
noncomputable def tent (x : ℝ) : ℝ := max (1 - |x|) 0

lemma tent_continuous : Continuous tent := by
  unfold tent; fun_prop

lemma tent_zero : tent 0 = 1 := by simp [tent]

lemma tent_eq_zero {x : ℝ} (hx : 1 ≤ |x|) : tent x = 0 := by
  simp only [tent, max_eq_right_iff]
  linarith

lemma tent_integrable : Integrable (fun x : ℝ => (tent x : ℂ)) := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact Complex.continuous_ofReal.comp tent_continuous
  · apply HasCompactSupport.intro (isCompact_Icc (a := (-1 : ℝ)) (b := 1))
    intro x hx
    simp only [Set.mem_Icc, not_and_or, not_le] at hx
    have : tent x = 0 := by
      refine tent_eq_zero ?_
      rcases hx with h | h
      · exact le_abs.2 (Or.inr (by linarith))
      · exact le_abs.2 (Or.inl (by linarith))
    simp [this]

/-- Antiderivative computation: the integral of `(A + B x) exp (c x)`. -/
lemma integral_linear_mul_exp (c A B : ℂ) (hc : c ≠ 0) (a b : ℝ) :
    ∫ x in a..b, (A + B * (x : ℂ)) * Complex.exp (c * x)
      = (Complex.exp (c * b) * ((A + B * b) / c - B / c ^ 2))
        - (Complex.exp (c * a) * ((A + B * a) / c - B / c ^ 2)) := by
  have key : ∀ x : ℝ, HasDerivAt (fun t : ℝ => Complex.exp (c * t) * ((A + B * t) / c - B / c ^ 2))
      ((A + B * (x : ℂ)) * Complex.exp (c * x)) x := by
    intro x
    have h0 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 x := Complex.ofRealCLM.hasDerivAt
    have h1 : HasDerivAt (fun t : ℝ => Complex.exp (c * t)) (Complex.exp (c * x) * c) x := by
      simpa using (h0.const_mul c).cexp
    have h2 : HasDerivAt (fun t : ℝ => (A + B * (t : ℂ)) / c - B / c ^ 2) (B / c) x := by
      simpa using (((h0.const_mul B).const_add A).div_const c).sub_const (B / c ^ 2)
    have h3 := h1.mul h2
    convert h3 using 1
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => key x)]
  exact Continuous.intervalIntegrable (by fun_prop) a b

/-- The Fourier integral of the tent function, reduced to an integral over `[-1, 1]`. -/
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
lemma fourier_tent (ξ : ℝ) :
    𝓕 (fun x : ℝ => (tent x : ℂ)) ξ = ((Real.sinc (π * ξ)) ^ 2 : ℝ) := by
  rw [fourier_tent_interval]
  have hsplit : (∫ x in (-1 : ℝ)..1, Complex.exp (↑(-2 * π * x * ξ) * Complex.I) • (tent x : ℂ))
      = (∫ x in (-1 : ℝ)..0, Complex.exp (↑(-2 * π * x * ξ) * Complex.I) • (tent x : ℂ))
        + ∫ x in (0 : ℝ)..1, Complex.exp (↑(-2 * π * x * ξ) * Complex.I) • (tent x : ℂ) := by
    rw [intervalIntegral.integral_add_adjacent_intervals] <;>
      exact Continuous.intervalIntegrable
        (Continuous.smul (by fun_prop) (Complex.continuous_ofReal.comp tent_continuous)) _ _
  rcases eq_or_ne ξ 0 with hξ | hξ
  · -- the value at `ξ = 0` is the total mass of the tent function, namely `1`
    subst hξ
    have h1 : (∫ x in (-1 : ℝ)..0, Complex.exp (↑(-2 * π * x * (0 : ℝ)) * Complex.I)
        • (tent x : ℂ)) = ∫ x in (-1 : ℝ)..0, ((1 + x : ℝ) : ℂ) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le (by norm_num)] at hx
      show Complex.exp (↑(-2 * π * x * (0 : ℝ)) * Complex.I) • (tent x : ℂ) = ((1 + x : ℝ) : ℂ)
      simp only [tent, abs_of_nonpos hx.2, mul_zero, Complex.ofReal_zero, zero_mul,
        Complex.exp_zero, one_smul]
      rw [max_eq_left (by linarith [hx.1])]
      push_cast; ring
    have h2 : (∫ x in (0 : ℝ)..1, Complex.exp (↑(-2 * π * x * (0 : ℝ)) * Complex.I)
        • (tent x : ℂ)) = ∫ x in (0 : ℝ)..1, ((1 - x : ℝ) : ℂ) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le (by norm_num)] at hx
      show Complex.exp (↑(-2 * π * x * (0 : ℝ)) * Complex.I) • (tent x : ℂ) = ((1 - x : ℝ) : ℂ)
      simp only [tent, abs_of_nonneg hx.1, mul_zero, Complex.ofReal_zero, zero_mul,
        Complex.exp_zero, one_smul]
      rw [max_eq_left (by linarith [hx.2])]
    have e1 : (∫ x in (-1:ℝ)..0, (1 + x)) = 1/2 := by
      rw [intervalIntegral.integral_add (_root_.intervalIntegrable_const)
        intervalIntegral.intervalIntegrable_id]
      simp [integral_id]
      norm_num
    have e2 : (∫ x in (0:ℝ)..1, (1 - x)) = 1/2 := by
      rw [intervalIntegral.integral_sub (_root_.intervalIntegrable_const)
        intervalIntegral.intervalIntegrable_id]
      simp [integral_id]
      norm_num
    rw [hsplit, h1, h2, intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal,
      e1, e2]
    norm_num
  · -- the generic case: an explicit antiderivative computation
    set c : ℂ := -2 * π * ξ * Complex.I with hc
    have hcne : c ≠ 0 := by simp [hc, Real.pi_ne_zero, hξ, Complex.ext_iff]
    have h1 : (∫ x in (-1 : ℝ)..0, Complex.exp (↑(-2 * π * x * ξ) * Complex.I) • (tent x : ℂ))
        = ∫ x in (-1 : ℝ)..0, (1 + 1 * (x : ℂ)) * Complex.exp (c * x) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le (by norm_num)] at hx
      have ht : (tent x : ℂ) = 1 + 1 * (x : ℂ) := by
        simp only [tent, abs_of_nonpos hx.2]
        rw [max_eq_left (by linarith [hx.1])]
        push_cast; ring
      show Complex.exp (↑(-2 * π * x * ξ) * Complex.I) • (tent x : ℂ)
          = (1 + 1 * (x : ℂ)) * Complex.exp (c * x)
      rw [smul_eq_mul, ht, mul_comm]
      congr 1
      push_cast [hc]
      ring_nf
    have h2 : (∫ x in (0 : ℝ)..1, Complex.exp (↑(-2 * π * x * ξ) * Complex.I) • (tent x : ℂ))
        = ∫ x in (0 : ℝ)..1, (1 + (-1) * (x : ℂ)) * Complex.exp (c * x) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le (by norm_num)] at hx
      have ht : (tent x : ℂ) = 1 + (-1) * (x : ℂ) := by
        simp only [tent, abs_of_nonneg hx.1]
        rw [max_eq_left (by linarith [hx.2])]
        push_cast; ring
      show Complex.exp (↑(-2 * π * x * ξ) * Complex.I) • (tent x : ℂ)
          = (1 + (-1) * (x : ℂ)) * Complex.exp (c * x)
      rw [smul_eq_mul, ht, mul_comm]
      congr 1
      push_cast [hc]
      ring_nf
    rw [hsplit, h1, h2, integral_linear_mul_exp c 1 1 hcne, integral_linear_mul_exp c 1 (-1) hcne]
    have hsum : (Complex.exp (c * ((0 : ℝ) : ℂ)) * ((1 + 1 * ((0 : ℝ) : ℂ)) / c - 1 / c ^ 2)
        - Complex.exp (c * ((-1 : ℝ) : ℂ)) * ((1 + 1 * ((-1 : ℝ) : ℂ)) / c - 1 / c ^ 2))
        + (Complex.exp (c * ((1 : ℝ) : ℂ)) * ((1 + (-1) * ((1 : ℝ) : ℂ)) / c - (-1) / c ^ 2)
        - Complex.exp (c * ((0 : ℝ) : ℂ)) * ((1 + (-1) * ((0 : ℝ) : ℂ)) / c - (-1) / c ^ 2))
        = (Complex.exp c + Complex.exp (-c) - 2) / c ^ 2 := by
      push_cast
      simp only [mul_zero, Complex.exp_zero, mul_one, mul_neg_one]
      field_simp
      ring
    rw [hsum, Real.sinc_of_ne_zero (mul_ne_zero Real.pi_ne_zero hξ), hc]
    -- finish with the trigonometric identity `2 - 2 cos (2πξ) = 4 sin² (πξ)`
    have hpx : (π : ℝ) * ξ ≠ 0 := mul_ne_zero Real.pi_ne_zero hξ
    have hcos : Real.cos (2 * π * ξ) = 1 - 2 * Real.sin (π * ξ) ^ 2 := by
      have h1 := Real.cos_two_mul (π * ξ)
      have h2 := Real.sin_sq_add_cos_sq (π * ξ)
      rw [show 2 * π * ξ = 2 * (π * ξ) by ring, h1]
      nlinarith
    have hexp : Complex.exp (-2 * (π : ℂ) * ξ * Complex.I)
        + Complex.exp (-(-2 * (π : ℂ) * ξ * Complex.I)) = 2 * (Real.cos (2 * π * ξ) : ℂ) := by
      rw [Complex.ofReal_cos, Complex.two_cos]
      push_cast
      ring_nf
    rw [hexp, hcos]
    have hI : (Complex.I) ^ 2 = -1 := Complex.I_sq
    push_cast
    field_simp
    ring_nf
    rw [hI]
    ring

/-! ### Integrability of `sinc²` -/

lemma sinc_sq_le (x : ℝ) : Real.sinc x ^ 2 ≤ 2 * (1 + x ^ 2)⁻¹ := by
  have h1 : Real.sinc x ^ 2 ≤ 1 := by
    have := Real.abs_sinc_le_one x
    nlinarith [abs_nonneg (Real.sinc x), sq_abs (Real.sinc x)]
  rcases le_or_gt (x ^ 2) 1 with h | h
  · have : (1 : ℝ) ≤ 2 * (1 + x ^ 2)⁻¹ := by
      rw [le_mul_inv_iff₀ (by positivity)]; linarith
    linarith
  · have hx : x ≠ 0 := by intro h0; rw [h0] at h; norm_num at h
    have hs : Real.sinc x ^ 2 = Real.sin x ^ 2 / x ^ 2 := by
      rw [Real.sinc_of_ne_zero hx]; ring
    have hsin : Real.sin x ^ 2 ≤ 1 := by
      nlinarith [Real.neg_one_le_sin x, Real.sin_le_one x]
    have h2 : Real.sinc x ^ 2 ≤ 1 / x ^ 2 := by
      rw [hs]; gcongr
    have h3 : 1 / x ^ 2 ≤ 2 * (1 + x ^ 2)⁻¹ := by
      rw [← div_eq_mul_inv, div_le_div_iff₀ (by nlinarith) (by positivity)]
      nlinarith
    linarith

lemma integrable_sinc_sq : Integrable (fun x : ℝ => Real.sinc x ^ 2) := by
  refine Integrable.mono' (g := fun x : ℝ => 2 * (1 + x ^ 2)⁻¹)
    (integrable_inv_one_add_sq.const_mul 2) (by fun_prop) (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact sinc_sq_le x

lemma integrable_sinc_pi_sq : Integrable (fun ξ : ℝ => Real.sinc (π * ξ) ^ 2) :=
  integrable_sinc_sq.comp_mul_left' Real.pi_ne_zero

/-! ### The value of the integral -/

/-- Fourier inversion at `0` applied to the tent function. -/
lemma integral_sinc_pi_sq : ∫ ξ : ℝ, Real.sinc (π * ξ) ^ 2 = 1 := by
  have hFint : Integrable (𝓕 (fun x : ℝ => (tent x : ℂ))) := by
    have : (𝓕 (fun x : ℝ => (tent x : ℂ))) = fun ξ : ℝ => ((Real.sinc (π * ξ) ^ 2 : ℝ) : ℂ) := by
      funext ξ; exact fourier_tent ξ
    rw [this]
    exact integrable_sinc_pi_sq.ofReal
  have hinv := tent_integrable.fourierInv_fourier_eq (v := 0) hFint
    ((Complex.continuous_ofReal.comp tent_continuous).continuousAt)
  rw [Real.fourierInv_eq'] at hinv
  simp only [inner_zero_right, mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
    one_smul, tent_zero, Complex.ofReal_one] at hinv
  rw [show (fun ξ : ℝ => 𝓕 (fun x : ℝ => (tent x : ℂ)) ξ)
      = fun ξ : ℝ => ((Real.sinc (π * ξ) ^ 2 : ℝ) : ℂ) from funext fourier_tent] at hinv
  have hco : ((∫ ξ : ℝ, Real.sinc (π * ξ) ^ 2 : ℝ) : ℂ)
      = ∫ ξ : ℝ, ((Real.sinc (π * ξ) ^ 2 : ℝ) : ℂ) :=
    (Complex.ofRealCLM.integral_comp_comm integrable_sinc_pi_sq).symm
  have hcast : ((∫ ξ : ℝ, Real.sinc (π * ξ) ^ 2 : ℝ) : ℂ) = 1 := hco.trans hinv
  exact_mod_cast hcast

theorem integral_sinc_sq : ∫ x : ℝ, (Real.sin x / x) ^ 2 = π := by
  have hscale : ∫ ξ : ℝ, Real.sinc (π * ξ) ^ 2 = |π⁻¹| • ∫ x : ℝ, Real.sinc x ^ 2 :=
    MeasureTheory.Measure.integral_comp_mul_left (fun x : ℝ => Real.sinc x ^ 2) π
  rw [integral_sinc_pi_sq, abs_of_pos (by positivity : (0:ℝ) < π⁻¹), smul_eq_mul] at hscale
  have hval : ∫ x : ℝ, Real.sinc x ^ 2 = π := by
    field_simp at hscale
    linarith
  rw [← hval]
  refine MeasureTheory.integral_congr_ae ?_
  have hae : ∀ᵐ x : ℝ, x ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    simp
  filter_upwards [hae] with x hx
  rw [Real.sinc_of_ne_zero hx]

end Zeta23Scaffold

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

