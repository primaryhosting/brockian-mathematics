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

The Dirichlet-type integral `∫_ℝ (sin x / x)^2 dx = π`.

The proof goes through the Fourier inversion formula applied to the triangle function
`tri ξ = max (1 - |ξ|) 0`, whose Fourier transform is `x ↦ sinc (π x)^2`.
-/

open MeasureTheory Real intervalIntegral
open scoped FourierTransform RealInnerProductSpace

namespace Zeta23Scaffold

/-- The triangle function `ξ ↦ max (1 - |ξ|) 0`, viewed as a complex-valued function. -/
noncomputable def tri (x : ℝ) : ℂ := ((max (1 - |x|) 0 : ℝ) : ℂ)

lemma tri_continuous : Continuous tri := by
  unfold tri
  fun_prop

lemma tri_support {x : ℝ} (hx : 1 ≤ |x|) : tri x = 0 := by
  simp only [tri, Complex.ofReal_eq_zero, max_eq_right_iff]
  linarith

lemma tri_integrable : Integrable tri := by
  apply tri_continuous.integrable_of_hasCompactSupport
  apply HasCompactSupport.intro (isCompact_Icc (a := (-1 : ℝ)) (b := 1))
  intro x hx
  apply tri_support
  simp only [Set.mem_Icc, not_and_or, not_le] at hx
  rcases hx with h | h
  · rw [abs_of_nonpos (by linarith)]; linarith
  · rw [abs_of_nonneg (by linarith)]; linarith

/-- Antiderivative computation: `∫_0^1 (1 - ξ) e^{aξ} dξ = (e^a - a - 1)/a^2`. -/
lemma integral_one_sub_mul_exp {a : ℂ} (ha : a ≠ 0) :
    (∫ ξ in (0:ℝ)..1, (1 - (ξ:ℂ)) * Complex.exp (a * ξ)) =
      (Complex.exp a - a - 1) / a ^ 2 := by
  have key : ∀ ξ ∈ Set.uIcc (0:ℝ) 1, HasDerivAt
      (fun t : ℝ => (1 - (t:ℂ)) * Complex.exp (a * t) / a + Complex.exp (a * t) / a ^ 2)
      ((1 - (ξ:ℂ)) * Complex.exp (a * ξ)) ξ := by
    intro ξ _
    have h1 : HasDerivAt (fun t : ℝ => (t:ℂ)) 1 ξ := Complex.ofRealCLM.hasDerivAt
    have h2 : HasDerivAt (fun t : ℝ => Complex.exp (a * t)) (a * Complex.exp (a * ξ)) ξ := by
      have := (Complex.hasDerivAt_exp (a * ξ)).comp ξ (h1.const_mul a)
      simpa [mul_comm] using this
    have h3 : HasDerivAt (fun t : ℝ => (1 - (t:ℂ)) * Complex.exp (a * t))
        (-1 * Complex.exp (a * ξ) + (1 - (ξ:ℂ)) * (a * Complex.exp (a * ξ))) ξ :=
      ((h1.const_sub 1).mul h2)
    have := (h3.div_const a).add (h2.div_const (a ^ 2))
    convert this using 1
    field_simp
    ring
  rw [integral_eq_sub_of_hasDerivAt key]
  · push_cast
    simp only [mul_zero, Complex.exp_zero]
    field_simp
    ring
  · apply Continuous.intervalIntegrable
    fun_prop

/-- Antiderivative computation: `∫_{-1}^0 (1 + ξ) e^{aξ} dξ = (a - 1 + e^{-a})/a^2`. -/
lemma integral_one_add_mul_exp {a : ℂ} (ha : a ≠ 0) :
    (∫ ξ in (-1:ℝ)..0, (1 + (ξ:ℂ)) * Complex.exp (a * ξ)) =
      (a - 1 + Complex.exp (-a)) / a ^ 2 := by
  have key : ∀ ξ ∈ Set.uIcc (-1:ℝ) 0, HasDerivAt
      (fun t : ℝ => (1 + (t:ℂ)) * Complex.exp (a * t) / a - Complex.exp (a * t) / a ^ 2)
      ((1 + (ξ:ℂ)) * Complex.exp (a * ξ)) ξ := by
    intro ξ _
    have h1 : HasDerivAt (fun t : ℝ => (t:ℂ)) 1 ξ := Complex.ofRealCLM.hasDerivAt
    have h2 : HasDerivAt (fun t : ℝ => Complex.exp (a * t)) (a * Complex.exp (a * ξ)) ξ := by
      have := (Complex.hasDerivAt_exp (a * ξ)).comp ξ (h1.const_mul a)
      simpa [mul_comm] using this
    have h3 : HasDerivAt (fun t : ℝ => (1 + (t:ℂ)) * Complex.exp (a * t))
        (1 * Complex.exp (a * ξ) + (1 + (ξ:ℂ)) * (a * Complex.exp (a * ξ))) ξ :=
      ((h1.const_add 1).mul h2)
    have := (h3.div_const a).sub (h2.div_const (a ^ 2))
    convert this using 1
    field_simp
    ring
  rw [integral_eq_sub_of_hasDerivAt key]
  · push_cast
    simp only [mul_zero, Complex.exp_zero, mul_neg, mul_one]
    field_simp
    ring
  · apply Continuous.intervalIntegrable
    fun_prop

/-- The integral of `e^{a v} · tri v` over `ℝ` as a sum of two interval integrals. -/
lemma integral_exp_mul_tri (a : ℂ) : (∫ v : ℝ, Complex.exp (a * v) * tri v) =
    (∫ ξ in (-1:ℝ)..0, (1 + (ξ:ℂ)) * Complex.exp (a * ξ)) +
    (∫ ξ in (0:ℝ)..1, (1 - (ξ:ℂ)) * Complex.exp (a * ξ)) := by
  have hzero : ∀ v : ℝ, v ∉ Set.Ioc (-1:ℝ) 1 → Complex.exp (a * v) * tri v = 0 := by
    intro v hv
    simp only [Set.mem_Ioc, not_and_or, not_lt, not_le] at hv
    have : (1:ℝ) ≤ |v| := by
      rcases hv with h | h
      · rw [abs_of_nonpos (by linarith)]; linarith
      · rw [abs_of_nonneg (by linarith)]; linarith
    rw [tri_support this, mul_zero]
  rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hzero,
    ← intervalIntegral.integral_of_le (by norm_num : (-1:ℝ) ≤ 1),
    ← intervalIntegral.integral_add_adjacent_intervals
      (a := (-1:ℝ)) (b := 0) (c := 1) ?_ ?_]
  · congr 1
    · apply intervalIntegral.integral_congr
      intro v hv
      rw [Set.uIcc_of_le (by norm_num : (-1:ℝ) ≤ 0)] at hv
      simp only [Set.mem_Icc] at hv
      have hv' : |v| = -v := abs_of_nonpos hv.2
      simp only [tri, hv']
      rw [max_eq_left (by linarith [hv.1])]
      push_cast
      ring
    · apply intervalIntegral.integral_congr
      intro v hv
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hv
      simp only [Set.mem_Icc] at hv
      have hv' : |v| = v := abs_of_nonneg hv.1
      simp only [tri, hv']
      rw [max_eq_left (by linarith [hv.2])]
      push_cast
      ring
  · apply Continuous.intervalIntegrable
    exact Continuous.mul (by fun_prop) tri_continuous
  · apply Continuous.intervalIntegrable
    exact Continuous.mul (by fun_prop) tri_continuous

lemma fourier_tri_eq_integral (x : ℝ) :
    𝓕 tri x = ∫ v : ℝ, Complex.exp (((-2 * π * x : ℝ) : ℂ) * Complex.I * v) * tri v := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  congr 1 with v
  rw [smul_eq_mul]
  congr 2
  push_cast
  ring

/-- The key arithmetic identity behind the Fourier transform of the triangle function. -/
lemma exp_sum_div_sq (x : ℝ) (hx : x ≠ 0) :
    (Complex.exp (((-2 * π * x : ℝ) : ℂ) * Complex.I)
      + Complex.exp (-(((-2 * π * x : ℝ) : ℂ) * Complex.I)) - 2)
      / (((-2 * π * x : ℝ) : ℂ) * Complex.I) ^ 2 = ((Real.sinc (π * x) ^ 2 : ℝ) : ℂ) := by
  set θ : ℝ := -2 * π * x with hθ
  have e1 : Complex.exp ((θ : ℂ) * Complex.I)
      = (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I := by
    rw [Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
  have e2 : -((θ : ℂ) * Complex.I) = ((-θ : ℝ) : ℂ) * Complex.I := by push_cast; ring
  have e3 : Complex.exp (((-θ : ℝ) : ℂ) * Complex.I)
      = (Real.cos θ : ℂ) - (Real.sin θ : ℂ) * Complex.I := by
    rw [Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
    push_cast
    rw [Complex.cos_neg, Complex.sin_neg]
    ring
  rw [e1, e2, e3]
  have hsq : ((θ : ℂ) * Complex.I) ^ 2 = ((-(θ ^ 2) : ℝ) : ℂ) := by
    push_cast
    rw [mul_pow, Complex.I_sq]
    ring
  rw [hsq]
  have hnum : (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I
      + ((Real.cos θ : ℂ) - (Real.sin θ : ℂ) * Complex.I) - 2
      = ((2 * Real.cos θ - 2 : ℝ) : ℂ) := by push_cast; ring
  rw [hnum, ← Complex.ofReal_div]
  norm_cast
  have hπx : π * x ≠ 0 := mul_ne_zero Real.pi_ne_zero hx
  rw [Real.sinc_of_ne_zero hπx]
  have hcos : Real.cos θ = 1 - 2 * Real.sin (π * x) ^ 2 := by
    have h : θ = -(2 * (π * x)) := by rw [hθ]; ring
    rw [h, Real.cos_neg, Real.cos_two_mul, ← Real.sin_sq_add_cos_sq (π * x)]
    ring
  rw [hcos]
  have hθ2 : θ ^ 2 = 4 * (π * x) ^ 2 := by rw [hθ]; ring
  rw [hθ2]
  field_simp
  ring

/-- The Fourier transform of the triangle function is `x ↦ sinc (π x) ^ 2`. -/
lemma fourier_tri (x : ℝ) : 𝓕 tri x = ((Real.sinc (π * x) ^ 2 : ℝ) : ℂ) := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [fourier_tri_eq_integral]
    simp only [mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul]
    rw [show (∫ v : ℝ, tri v) = ∫ v : ℝ, Complex.exp ((0 : ℂ) * v) * tri v by simp,
      integral_exp_mul_tri]
    norm_num
    rw [show (∫ ξ in (-1:ℝ)..0, (1 + (ξ:ℂ))) = ((∫ ξ in (-1:ℝ)..0, (1 + ξ) : ℝ) : ℂ) by
        rw [← intervalIntegral.integral_ofReal]; push_cast; ring_nf,
      show (∫ ξ in (0:ℝ)..1, (1 - (ξ:ℂ))) = ((∫ ξ in (0:ℝ)..1, (1 - ξ) : ℝ) : ℂ) by
        rw [← intervalIntegral.integral_ofReal]; push_cast; ring_nf]
    rw [intervalIntegral.integral_add _root_.intervalIntegrable_const
        intervalIntegral.intervalIntegrable_id,
      intervalIntegral.integral_sub _root_.intervalIntegrable_const
        intervalIntegral.intervalIntegrable_id]
    simp only [intervalIntegral.integral_const, integral_id, smul_eq_mul]
    norm_num
  · set a : ℂ := ((-2 * π * x : ℝ) : ℂ) * Complex.I with ha
    have hreal : (-2 * π * x : ℝ) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hx
    have ha0 : a ≠ 0 :=
      mul_ne_zero (Complex.ofReal_ne_zero.mpr hreal) Complex.I_ne_zero
    rw [fourier_tri_eq_integral, integral_exp_mul_tri a, integral_one_add_mul_exp ha0,
      integral_one_sub_mul_exp ha0, ← add_div, ← exp_sum_div_sq x hx]
    rw [ha]
    ring_nf

lemma integrable_sinc_sq : Integrable (fun x : ℝ => Real.sinc x ^ 2) := by
  have hg : Integrable (fun x : ℝ => 2 * (1 + x ^ 2)⁻¹) := integrable_inv_one_add_sq.const_mul 2
  refine Integrable.mono' hg ((Real.continuous_sinc.pow 2).aestronglyMeasurable) ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  by_cases h : |x| ≤ 1
  · have h1 : Real.sinc x ^ 2 ≤ 1 := by
      have := Real.abs_sinc_le_one x
      nlinarith [abs_nonneg (Real.sinc x), sq_abs (Real.sinc x)]
    have h2 : (1:ℝ) ≤ 2 * (1 + x ^ 2)⁻¹ := by
      have hx2 : x ^ 2 ≤ 1 := by nlinarith [abs_nonneg x, sq_abs x]
      rw [le_mul_inv_iff₀ (by positivity)]
      linarith
    linarith
  · push_neg at h
    have hx0 : x ≠ 0 := by
      intro h0
      rw [h0] at h
      simp only [abs_zero] at h
      linarith
    have h1 : Real.sinc x ^ 2 ≤ (x ^ 2)⁻¹ := by
      rw [Real.sinc_of_ne_zero hx0, div_pow, div_le_iff₀ (by positivity)]
      have : Real.sin x ^ 2 ≤ 1 := by nlinarith [Real.neg_one_le_sin x, Real.sin_le_one x]
      rw [inv_mul_cancel₀ (by positivity)]
      exact this
    have h2 : (x ^ 2)⁻¹ ≤ 2 * (1 + x ^ 2)⁻¹ := by
      have hx2 : 1 < x ^ 2 := by nlinarith [abs_nonneg x, sq_abs x]
      have hpos : (0:ℝ) < x ^ 2 := by linarith
      have key : 2 * (1 + x ^ 2)⁻¹ - (x ^ 2)⁻¹
          = (2 * x ^ 2 - (1 + x ^ 2)) / ((1 + x ^ 2) * x ^ 2) := by
        field_simp
      have hnn : 0 ≤ 2 * (1 + x ^ 2)⁻¹ - (x ^ 2)⁻¹ := by
        rw [key]
        apply div_nonneg (by linarith) (by positivity)
      linarith
    linarith

lemma integrable_fourier_tri : Integrable (𝓕 tri) := by
  have h : Integrable (fun x : ℝ => ((Real.sinc (π * x) ^ 2 : ℝ) : ℂ)) := by
    apply MeasureTheory.Integrable.ofReal
    exact integrable_sinc_sq.comp_mul_left' Real.pi_ne_zero
  apply h.congr
  filter_upwards with x
  rw [fourier_tri]

lemma integral_sinc_sq_pi_mul : (∫ x : ℝ, Real.sinc (π * x) ^ 2) = 1 := by
  have hinv := tri_continuous.fourierInv_fourier_eq tri_integrable integrable_fourier_tri
  have h0 : 𝓕⁻ (𝓕 tri) 0 = tri 0 := by rw [hinv]
  rw [Real.fourierInv_eq'] at h0
  simp only [inner_zero_right, mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
    one_smul] at h0
  have h1 : (∫ v : ℝ, 𝓕 tri v) = ((∫ v : ℝ, Real.sinc (π * v) ^ 2 : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    exact MeasureTheory.integral_congr_ae (by filter_upwards with v using fourier_tri v)
  rw [h1] at h0
  have htri0 : tri 0 = 1 := by norm_num [tri]
  rw [htri0] at h0
  exact_mod_cast h0

lemma integral_sinc_sq' : (∫ x : ℝ, Real.sinc x ^ 2) = π := by
  have h := MeasureTheory.Measure.integral_comp_mul_left (fun y : ℝ => Real.sinc y ^ 2) π
  rw [integral_sinc_sq_pi_mul] at h
  rw [smul_eq_mul, abs_of_pos (by positivity : (0:ℝ) < π⁻¹)] at h
  field_simp at h
  linarith [h]

/-- The normalization integral of the sine kernel: `∫_ℝ (sin x / x)^2 dx = π`. -/
theorem integral_sinc_sq : (∫ x : ℝ, (Real.sin x / x) ^ 2) = π := by
  rw [← integral_sinc_sq']
  apply MeasureTheory.integral_congr_ae
  have hae : {(0:ℝ)}ᶜ ∈ ae (volume : Measure ℝ) := compl_mem_ae_iff.mpr Real.volume_singleton
  filter_upwards [hae] with x hx
  rw [Real.sinc_of_ne_zero (by simpa using hx)]

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

