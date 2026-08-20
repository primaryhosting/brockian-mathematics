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

theorem integral_lin_mul_cexp (a b : ℝ) (p q c : ℂ) (hc : c ≠ 0) :
    ∫ t in a..b, (p + q * (t : ℂ)) * Complex.exp (c * t) =
      (((p + q * b) / c - q / c ^ 2) * Complex.exp (c * b))
        - (((p + q * a) / c - q / c ^ 2) * Complex.exp (c * a)) := by
  have key : ∀ t : ℝ,
      HasDerivAt (fun t : ℝ => ((p + q * (t : ℂ)) / c - q / c ^ 2) * Complex.exp (c * t))
        ((p + q * (t : ℂ)) * Complex.exp (c * t)) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
    have h2 : HasDerivAt (fun t : ℝ => Complex.exp (c * t)) (Complex.exp (c * t) * c) t := by
      simpa using (h1.const_mul c).cexp
    have h3 : HasDerivAt (fun t : ℝ => ((p + q * (t : ℂ)) / c - q / c ^ 2)) (q / c) t := by
      simpa using (((h1.const_mul q).const_add p).div_const c).sub_const (q / c ^ 2)
    have := h3.mul h2
    convert this using 1
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => key t)]
  exact Continuous.intervalIntegrable (by fun_prop) _ _

/-- The tent function on `[-1, 1]`, valued in `ℂ`. -/

noncomputable def tentC : ℝ → ℂ := fun t => ((max 0 (1 - |t|) : ℝ) : ℂ)

/-- The square of the sinc function, rescaled by `π`, valued in `ℂ`.  This is the Fourier
transform of the tent function. -/

noncomputable def sincSqC : ℝ → ℂ := fun ξ => ((Real.sinc (π * ξ) ^ 2 : ℝ) : ℂ)

@[fun_prop] lemma continuous_tentC : Continuous tentC := by unfold tentC; fun_prop

lemma tent_eq_zero_of_notMem {t : ℝ} (ht : t ∉ Set.Icc (-1 : ℝ) 1) : max 0 (1 - |t|) = 0 := by
  simp only [Set.mem_Icc, not_and_or, not_le] at ht
  rcases ht with h | h
  · have : 1 ≤ |t| := by rw [abs_of_nonpos (by linarith)]; linarith
    simp [sub_nonpos.2 this]
  · have : 1 ≤ |t| := le_trans (by linarith) (le_abs_self t)
    simp [sub_nonpos.2 this]

lemma tentC_eq_zero_of_notMem {t : ℝ} (ht : t ∉ Set.Icc (-1 : ℝ) 1) : tentC t = 0 := by
  simp [tentC, tent_eq_zero_of_notMem ht]

lemma hasCompactSupport_tentC : HasCompactSupport tentC :=
  HasCompactSupport.intro isCompact_Icc (fun _ hx => tentC_eq_zero_of_notMem hx)

lemma integrable_tentC : Integrable tentC :=
  continuous_tentC.integrable_of_hasCompactSupport hasCompactSupport_tentC

lemma tentC_neg (t : ℝ) : tentC (-t) = tentC t := by simp [tentC]

lemma continuous_sincSqC : Continuous sincSqC := by
  unfold sincSqC
  exact Complex.continuous_ofReal.comp (((Real.continuous_sinc.comp
    (continuous_const.mul continuous_id)).pow 2))

lemma integrable_sincSqC : Integrable sincSqC := by
  have hbound : ∀ ξ : ℝ, ‖sincSqC ξ‖ ≤ 2 * (1 + ξ ^ 2)⁻¹ := by
    intro ξ
    have h1 : ‖sincSqC ξ‖ = Real.sinc (π * ξ) ^ 2 := by
      simp [sincSqC, Complex.norm_real]
    rw [h1]
    have hle1 : Real.sinc (π * ξ) ^ 2 ≤ 1 := by
      have := Real.abs_sinc_le_one (π * ξ)
      nlinarith [abs_nonneg (Real.sinc (π * ξ)), sq_abs (Real.sinc (π * ξ))]
    have hpos : (0 : ℝ) < 1 + ξ ^ 2 := by positivity
    rw [show (2 : ℝ) * (1 + ξ ^ 2)⁻¹ = 2 / (1 + ξ ^ 2) by ring, le_div_iff₀ hpos]
    rcases eq_or_ne ξ 0 with rfl | hξ
    · norm_num
    · have hpx : π * ξ ≠ 0 := mul_ne_zero Real.pi_ne_zero hξ
      have h2 : Real.sinc (π * ξ) ^ 2 * (π * ξ) ^ 2 = Real.sin (π * ξ) ^ 2 := by
        rw [Real.sinc_of_ne_zero hpx]; field_simp
      have h3 : Real.sinc (π * ξ) ^ 2 * (π * ξ) ^ 2 ≤ 1 := by
        rw [h2]; nlinarith [Real.neg_one_le_sin (π * ξ), Real.sin_le_one (π * ξ)]
      have hπ : (1 : ℝ) ≤ π ^ 2 := by nlinarith [Real.pi_gt_three]
      have hξ2 : (0 : ℝ) < ξ ^ 2 := by positivity
      have hs : (0 : ℝ) ≤ Real.sinc (π * ξ) ^ 2 := sq_nonneg _
      nlinarith [mul_nonneg hs hξ2.le, mul_le_mul_of_nonneg_right hπ (mul_nonneg hs hξ2.le)]
  refine Integrable.mono' (g := fun ξ : ℝ => 2 * (1 + ξ ^ 2)⁻¹) ?_
    continuous_sincSqC.aestronglyMeasurable (Filter.Eventually.of_forall hbound)
  simpa using (integrable_inv_one_add_sq).const_mul 2

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

lemma fourier_tentC : 𝓕 tentC = sincSqC := by
  refine Continuous.ext_on (dense_compl_singleton (0 : ℝ))
    (VectorFourier.fourierIntegral_continuous (L := innerₗ ℝ) Real.continuous_fourierChar
      continuous_inner integrable_tentC) continuous_sincSqC (fun ξ hξ => ?_)
  exact fourier_tentC_apply_of_ne_zero ξ (by simpa using hξ)

lemma fourier_sincSqC : 𝓕 sincSqC = tentC := by
  have hint : Integrable (𝓕 tentC) := by rw [fourier_tentC]; exact integrable_sincSqC
  have h : 𝓕⁻ (𝓕 tentC) = tentC :=
    continuous_tentC.fourierInv_fourier_eq integrable_tentC hint
  funext x
  calc 𝓕 sincSqC x = 𝓕 (𝓕 tentC) x := by rw [fourier_tentC]
    _ = 𝓕⁻ (𝓕 tentC) (-x) := by rw [Real.fourierInv_eq_fourier_neg, neg_neg]
    _ = tentC (-x) := by rw [h]
    _ = tentC x := tentC_neg x

lemma integral_tent_sq : ∫ t : ℝ, (max 0 (1 - |t|) : ℝ) ^ 2 = 2 / 3 := by
  have hsupp : ∀ t : ℝ, t ∉ Set.Icc (-1 : ℝ) 1 → (max 0 (1 - |t|) : ℝ) ^ 2 = 0 := by
    intro t ht
    simp [tent_eq_zero_of_notMem ht]
  rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hsupp,
    MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
    ← intervalIntegral.integral_add_adjacent_intervals
      (b := (0 : ℝ)) (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _)]
  have h1 : (∫ t in (-1 : ℝ)..0, (max 0 (1 - |t|) : ℝ) ^ 2) = ∫ t in (-1 : ℝ)..0, (1 + t) ^ 2 := by
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 0)] at ht
    rw [abs_of_nonpos ht.2, max_eq_right (by linarith [ht.1])]
    ring_nf
  have h2 : (∫ t in (0 : ℝ)..1, (max 0 (1 - |t|) : ℝ) ^ 2) = ∫ t in (0 : ℝ)..1, (1 - t) ^ 2 := by
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    rw [abs_of_nonneg ht.1, max_eq_right (by linarith [ht.2])]
  have e1 : (∫ t in (-1 : ℝ)..0, (1 + t) ^ 2) = 1 / 3 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun t : ℝ => (1 + t) ^ 3 / 3) (fun t _ => by
        simpa using (((hasDerivAt_id t).const_add 1).pow 3).div_const 3)
      (Continuous.intervalIntegrable (by fun_prop) _ _)]
    norm_num
  have e2 : (∫ t in (0 : ℝ)..1, (1 - t) ^ 2) = 1 / 3 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun t : ℝ => -((1 - t) ^ 3 / 3)) (fun t _ => by
        have h := ((((hasDerivAt_id t).const_sub 1).pow 3).div_const 3).neg
        simp only [id] at h
        convert h using 1
        push_cast
        ring)
      (Continuous.intervalIntegrable (by fun_prop) _ _)]
    norm_num
  rw [h1, h2, e1, e2]
  norm_num

lemma integral_tentC_sq : ∫ t : ℝ, tentC t * tentC t = (2 / 3 : ℂ) := by
  have hfun : ∀ t : ℝ, tentC t * tentC t = (((max 0 (1 - |t|) : ℝ) ^ 2 : ℝ) : ℂ) := by
    intro t
    simp only [tentC, ← Complex.ofReal_mul]
    norm_cast
    ring
  simp_rw [hfun]
  rw [integral_complex_ofReal, integral_tent_sq]
  norm_num

lemma integral_sincSqC_sq : ∫ ξ : ℝ, sincSqC ξ * sincSqC ξ = (2 / 3 : ℂ) := by
  have hflip : ∫ ξ : ℝ, (𝓕 tentC ξ) * (sincSqC ξ) = ∫ x : ℝ, (tentC x) * (𝓕 sincSqC x) := by
    simpa [mul_comm] using (VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ ℝ)
      Real.continuous_fourierChar continuous_inner integrable_tentC integrable_sincSqC)
  rw [fourier_tentC] at hflip
  rw [hflip, fourier_sincSqC, integral_tentC_sq]

lemma integral_sinc_pi_fourth : ∫ ξ : ℝ, Real.sinc (π * ξ) ^ 4 = 2 / 3 := by
  have h : ((∫ ξ : ℝ, Real.sinc (π * ξ) ^ 4 : ℝ) : ℂ) = ((2 / 3 : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    have hfun : ∀ ξ : ℝ, ((Real.sinc (π * ξ) ^ 4 : ℝ) : ℂ) = sincSqC ξ * sincSqC ξ := by
      intro ξ; simp only [sincSqC, ← Complex.ofReal_mul]; norm_cast; ring
    simp_rw [hfun]
    rw [integral_sincSqC_sq]
    norm_num
  exact Complex.ofReal_inj.mp h

/-- The integral of the fourth power of the (unnormalized) sinc function `sin x / x`
over the real line equals `2 π / 3`. -/
