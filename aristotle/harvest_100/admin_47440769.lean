/-
# Integral Sinc Sq
Category: C Integral
Target: Zeta23Scaffold.integral_sinc_sq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Integral Sinc Sq
Category: C Integral
Target: Zeta23Scaffold.integral_sinc_sq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real
open MeasureTheory FourierTransform Complex intervalIntegral

set_option maxHeartbeats 1000000

namespace Zeta23Scaffold

/-- The triangle function `x ↦ max 0 (1 - |x|)`, viewed as a complex-valued function.
Its Fourier transform is the squared sinc kernel. -/
noncomputable def tri (x : ℝ) : ℂ := ((max 0 (1 - |x|) : ℝ) : ℂ)

lemma continuous_tri : Continuous tri := by
  unfold tri; fun_prop

lemma tri_eq_zero {x : ℝ} (hx : x ∉ Set.Ioc (-1 : ℝ) 1) : tri x = 0 := by
  simp only [Set.mem_Ioc, not_and_or, not_lt, not_le] at hx
  have h : 1 - |x| ≤ 0 := by
    rcases hx with h | h
    · rw [abs_of_nonpos (by linarith)]; linarith
    · rw [abs_of_nonneg (by linarith)]; linarith
  simp [tri, max_eq_left h]

lemma integrable_tri : Integrable tri := by
  apply Integrable.mono' (g := Set.indicator (Set.Icc (-1 : ℝ) 1) (fun _ => (1 : ℝ)))
  · exact (integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const (by simp))
  · exact continuous_tri.aestronglyMeasurable
  · filter_upwards with x
    by_cases hx : x ∈ Set.Icc (-1 : ℝ) 1
    · rw [Set.indicator_of_mem hx]
      simp only [tri, Complex.norm_real, Real.norm_eq_abs]
      simp only [Set.mem_Icc] at hx
      rw [abs_of_nonneg (le_max_left _ _)]
      rcases le_total x 0 with h | h
      · rw [abs_of_nonpos h]; simp; linarith [hx.1]
      · rw [abs_of_nonneg h]; simp; linarith [hx.2]
    · have hx' : x ∉ Set.Ioc (-1 : ℝ) 1 := fun hmem => hx ⟨hmem.1.le, hmem.2⟩
      rw [Set.indicator_of_notMem hx, tri_eq_zero hx']; simp

/-- Derivative of the generic antiderivative `v ↦ exp (b v) (A + B v)`. -/
lemma hasDerivAt_exp_linear (b A B : ℂ) (v : ℝ) :
    HasDerivAt (fun v : ℝ => Complex.exp (b * v) * (A + B * v))
      (b * Complex.exp (b * v) * (A + B * v) + Complex.exp (b * v) * B) v := by
  have h1 : HasDerivAt (fun v : ℝ => (v : ℂ)) 1 v := Complex.ofRealCLM.hasDerivAt
  have h2 : HasDerivAt (fun v : ℝ => Complex.exp (b * v)) (b * Complex.exp (b * v)) v := by
    simpa [mul_comm] using (h1.const_mul b).cexp
  have h3 : HasDerivAt (fun v : ℝ => A + B * v) B v := by
    simpa using (h1.const_mul B).const_add A
  simpa using h2.mul h3

lemma integral_exp_mul_one_sub (b : ℂ) (hb : b ≠ 0) :
    (∫ v in (0 : ℝ)..1, Complex.exp (b * v) * (1 - v)) =
      Complex.exp b / b ^ 2 - 1 / b - 1 / b ^ 2 := by
  have key : ∀ v : ℝ, HasDerivAt
      (fun v : ℝ => Complex.exp (b * v) * ((1 + 1 / b) / b + (-1 / b) * v))
      (Complex.exp (b * v) * (1 - v)) v := by
    intro v
    have h := hasDerivAt_exp_linear b ((1 + 1 / b) / b) (-1 / b) v
    convert h using 1
    field_simp
    ring
  have hcont : IntervalIntegrable (fun v : ℝ => Complex.exp (b * v) * (1 - v)) volume 0 1 := by
    apply Continuous.intervalIntegrable; fun_prop
  rw [integral_eq_sub_of_hasDerivAt (fun v _ => key v) hcont]
  simp only [Complex.ofReal_zero, Complex.ofReal_one, mul_zero, mul_one, Complex.exp_zero]
  field_simp
  ring

lemma integral_exp_mul_one_add (b : ℂ) (hb : b ≠ 0) :
    (∫ v in (-1 : ℝ)..0, Complex.exp (b * v) * (1 + v)) =
      1 / b - 1 / b ^ 2 + Complex.exp (-b) / b ^ 2 := by
  have key : ∀ v : ℝ, HasDerivAt
      (fun v : ℝ => Complex.exp (b * v) * ((1 - 1 / b) / b + (1 / b) * v))
      (Complex.exp (b * v) * (1 + v)) v := by
    intro v
    have h := hasDerivAt_exp_linear b ((1 - 1 / b) / b) (1 / b) v
    convert h using 1
    field_simp
    ring
  have hcont : IntervalIntegrable (fun v : ℝ => Complex.exp (b * v) * (1 + v)) volume (-1) 0 := by
    apply Continuous.intervalIntegrable; fun_prop
  rw [integral_eq_sub_of_hasDerivAt (fun v _ => key v) hcont]
  simp only [Complex.ofReal_zero, Complex.ofReal_one, Complex.ofReal_neg, mul_zero, mul_one,
    Complex.exp_zero, mul_neg]
  field_simp
  ring

/-- The Fourier transform of the triangle function is the squared sinc kernel. -/
lemma fourier_tri (ξ : ℝ) (hξ : ξ ≠ 0) :
    𝓕 tri ξ = ((Real.sin (π * ξ) / (π * ξ)) ^ 2 : ℝ) := by
  set b : ℂ := -(2 * π * ξ) * I with hbdef
  have hb : b ≠ 0 := by
    simp [hbdef, Complex.ext_iff, Real.pi_ne_zero, hξ]
  have h1 : 𝓕 tri ξ = ∫ v : ℝ, Complex.exp (b * v) * tri v := by
    rw [Real.fourier_real_eq_integral_exp_smul]
    congr 1
    funext v
    rw [smul_eq_mul]
    congr 2
    push_cast [hbdef]
    ring
  have hcont : Continuous (fun v : ℝ => Complex.exp (b * v) * tri v) :=
    (Complex.continuous_exp.comp (by fun_prop)).mul continuous_tri
  have h2 : (∫ v : ℝ, Complex.exp (b * v) * tri v)
      = ∫ v in (-1 : ℝ)..1, Complex.exp (b * v) * tri v := by
    rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero ?_).symm
    intro x hx
    rw [tri_eq_zero hx, mul_zero]
  have h3 : (∫ v in (-1 : ℝ)..1, Complex.exp (b * v) * tri v)
      = (∫ v in (-1 : ℝ)..0, Complex.exp (b * v) * tri v)
        + ∫ v in (0 : ℝ)..1, Complex.exp (b * v) * tri v :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)).symm
  have h4 : (∫ v in (-1 : ℝ)..0, Complex.exp (b * v) * tri v)
      = ∫ v in (-1 : ℝ)..0, Complex.exp (b * v) * (1 + v) := by
    apply intervalIntegral.integral_congr
    intro v hv
    rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 0), Set.mem_Icc] at hv
    have hva : |v| = -v := abs_of_nonpos hv.2
    simp only [tri, hva]
    rw [max_eq_right (by linarith [hv.1] : (0 : ℝ) ≤ 1 - -v)]
    push_cast
    ring
  have h5 : (∫ v in (0 : ℝ)..1, Complex.exp (b * v) * tri v)
      = ∫ v in (0 : ℝ)..1, Complex.exp (b * v) * (1 - v) := by
    apply intervalIntegral.integral_congr
    intro v hv
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1), Set.mem_Icc] at hv
    have hva : |v| = v := abs_of_nonneg hv.1
    simp only [tri, hva]
    rw [max_eq_right (by linarith [hv.2] : (0 : ℝ) ≤ 1 - v)]
    push_cast
    ring
  have hsum : 𝓕 tri ξ = (Complex.exp b + Complex.exp (-b) - 2) / b ^ 2 := by
    rw [h1, h2, h3, h4, h5, integral_exp_mul_one_add b hb, integral_exp_mul_one_sub b hb]
    field_simp
    ring
  -- Now evaluate the closed form.
  have hexp : Complex.exp b + Complex.exp (-b) = 2 * ((Real.cos (2 * π * ξ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cos, Complex.cos, hbdef]
    push_cast
    ring_nf
  have hb2 : b ^ 2 = -(((2 * π * ξ : ℝ) : ℂ)) ^ 2 := by
    rw [hbdef]
    push_cast
    ring_nf
    simp [Complex.I_sq]
  have hreal : (2 - 2 * Real.cos (2 * π * ξ)) / (2 * π * ξ) ^ 2
      = (Real.sin (π * ξ) / (π * ξ)) ^ 2 := by
    have hne : (π * ξ) ≠ 0 := mul_ne_zero Real.pi_ne_zero hξ
    have h := Real.cos_two_mul (π * ξ)
    have hs := Real.sin_sq_add_cos_sq (π * ξ)
    rw [show 2 * π * ξ = 2 * (π * ξ) by ring, h]
    field_simp
    nlinarith [hs]
  have hznz : ((2 * π * ξ : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    have : (2 : ℝ) * π * ξ ≠ 0 := by
      exact mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) hξ
    exact this
  rw [hsum, hexp, hb2, ← hreal]
  push_cast
  field_simp
  ring

lemma sinc_sq_le (x : ℝ) : (Real.sin x / x) ^ 2 ≤ 2 * (1 + x ^ 2)⁻¹ := by
  rcases eq_or_ne x 0 with rfl | hx
  · norm_num
  · have hx2 : (0 : ℝ) < x ^ 2 := by positivity
    rw [div_pow, div_le_iff₀ hx2]
    have h1 : Real.sin x ^ 2 ≤ x ^ 2 := by
      have := Real.abs_sin_le_abs (x := x)
      nlinarith [abs_nonneg x, abs_nonneg (Real.sin x), sq_abs x, sq_abs (Real.sin x)]
    have h2 : Real.sin x ^ 2 ≤ 1 := Real.sin_sq_le_one x
    have key : 2 * (1 + x ^ 2)⁻¹ * x ^ 2 = 2 * x ^ 2 / (1 + x ^ 2) := by field_simp
    rw [key, le_div_iff₀ (by positivity)]
    nlinarith

lemma integrable_sinc_sq : Integrable (fun x : ℝ => (Real.sin x / x) ^ 2) := by
  apply Integrable.mono' (g := fun x : ℝ => 2 * (1 + x ^ 2)⁻¹)
  · exact integrable_inv_one_add_sq.const_mul 2
  · exact Measurable.aestronglyMeasurable (by fun_prop)
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact sinc_sq_le x

lemma fourier_tri_ae :
    𝓕 tri =ᵐ[volume] fun ξ : ℝ => (((Real.sin (π * ξ) / (π * ξ)) ^ 2 : ℝ) : ℂ) := by
  filter_upwards [Measure.ae_ne volume (0 : ℝ)] with ξ hξ using fourier_tri ξ hξ

lemma integrable_fourier_tri : Integrable (𝓕 tri) := by
  rw [integrable_congr fourier_tri_ae]
  exact ((integrable_comp_mul_left_iff _ Real.pi_ne_zero).2 integrable_sinc_sq).ofReal

/-- The normalization integral of the sine kernel: `∫_ℝ (sin x / x)^2 dx = π`. -/
theorem integral_sinc_sq : ∫ x : ℝ, (Real.sin x / x) ^ 2 = π := by
  have hinv : 𝓕⁻ (𝓕 tri) = tri :=
    continuous_tri.fourierInv_fourier_eq integrable_tri integrable_fourier_tri
  have h0 : (∫ ξ : ℝ, 𝓕 tri ξ) = 1 := by
    have h := congrFun hinv 0
    rw [Real.fourierInv_eq] at h
    simpa [tri] using h
  have h1 : (∫ ξ : ℝ, (((Real.sin (π * ξ) / (π * ξ)) ^ 2 : ℝ) : ℂ)) = 1 := by
    rw [← integral_congr_ae fourier_tri_ae]; exact h0
  have h2 : (∫ ξ : ℝ, ((Real.sin (π * ξ) / (π * ξ)) ^ 2 : ℝ)) = 1 := by
    rw [integral_complex_ofReal] at h1
    exact_mod_cast h1
  have h3 := Measure.integral_comp_mul_left (fun x : ℝ => (Real.sin x / x) ^ 2) π
  rw [h2, abs_of_pos (show (0 : ℝ) < π⁻¹ by positivity), smul_eq_mul] at h3
  field_simp at h3
  simp_rw [div_pow]
  linarith [h3]

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

