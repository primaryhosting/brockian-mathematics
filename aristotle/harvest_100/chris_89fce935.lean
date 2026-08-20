import Mathlib

/-!
# Integral Sinc Sq
Category: C Integral
Target: Zeta23Scaffold.integral_sinc_sq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Complex Real
open scoped FourierTransform

namespace Zeta23Scaffold

/-- The triangle ("tent") function `x ↦ max (1 - |x|) 0`, viewed as a complex-valued function. -/
noncomputable def tri (x : ℝ) : ℂ := ((max (1 - |x|) 0 : ℝ) : ℂ)

@[fun_prop]
lemma tri_continuous : Continuous tri := by unfold tri; fun_prop

lemma tri_eq_zero_of_one_le_abs {x : ℝ} (hx : 1 ≤ |x|) : tri x = 0 := by
  simp only [tri, Complex.ofReal_eq_zero]
  exact max_eq_right (by linarith)

lemma tri_hasCompactSupport : HasCompactSupport tri := by
  apply HasCompactSupport.intro (isCompact_Icc (a := (-1 : ℝ)) (b := 1))
  intro x hx
  simp only [Set.mem_Icc, not_and_or, not_le] at hx
  refine tri_eq_zero_of_one_le_abs ?_
  rcases hx with h | h
  · exact le_abs.2 (Or.inr (by linarith))
  · exact le_abs.2 (Or.inl (by linarith))

lemma tri_integrable : Integrable tri :=
  tri_continuous.integrable_of_hasCompactSupport tri_hasCompactSupport

/-- An antiderivative of `t ↦ exp (c t) (1 + t)`. -/
lemma hasDerivAt_primitive_left (c : ℂ) (hc : c ≠ 0) (x : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.exp (c * t) * ((1 + (t : ℂ)) / c - 1 / c ^ 2))
      (Complex.exp (c * x) * (1 + (x : ℂ))) x := by
  have h1 : HasDerivAt (fun t : ℝ => c * (t : ℂ)) c x := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).const_mul c
  have he : HasDerivAt (fun t : ℝ => Complex.exp (c * t)) (c * Complex.exp (c * x)) x := by
    simpa [mul_comm] using h1.cexp
  have h2 : HasDerivAt (fun t : ℝ => (1 + (t : ℂ)) / c - 1 / c ^ 2) (1 / c) x := by
    have h3 : HasDerivAt (fun t : ℝ => (1 + (t : ℂ))) 1 x := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).const_add 1
    simpa using (h3.div_const c).sub_const (1 / c ^ 2)
  have h4 := he.mul h2
  convert h4 using 1
  field_simp; ring

/-- An antiderivative of `t ↦ exp (c t) (1 - t)`. -/
lemma hasDerivAt_primitive_right (c : ℂ) (hc : c ≠ 0) (x : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.exp (c * t) * ((1 - (t : ℂ)) / c + 1 / c ^ 2))
      (Complex.exp (c * x) * (1 - (x : ℂ))) x := by
  have h1 : HasDerivAt (fun t : ℝ => c * (t : ℂ)) c x := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).const_mul c
  have he : HasDerivAt (fun t : ℝ => Complex.exp (c * t)) (c * Complex.exp (c * x)) x := by
    simpa [mul_comm] using h1.cexp
  have h2 : HasDerivAt (fun t : ℝ => (1 - (t : ℂ)) / c + 1 / c ^ 2) (-1 / c) x := by
    have h3 : HasDerivAt (fun t : ℝ => (1 - (t : ℂ))) (-1) x := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).const_sub 1
    simpa [neg_div] using (h3.div_const c).add_const (1 / c ^ 2)
  have h4 := he.mul h2
  convert h4 using 1
  field_simp; ring

lemma integral_tri_exp_left (c : ℂ) (hc : c ≠ 0) :
    (∫ v in (-1 : ℝ)..0, Complex.exp (c * v) * tri v)
      = 1 / c - 1 / c ^ 2 + Complex.exp (-c) / c ^ 2 := by
  have hcong : ∫ v in (-1 : ℝ)..0, Complex.exp (c * v) * tri v
      = ∫ v in (-1 : ℝ)..0, Complex.exp (c * v) * (1 + (v : ℂ)) := by
    refine intervalIntegral.integral_congr ?_
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 0)] at hx
    obtain ⟨h1, h2⟩ := hx
    have habs : |x| = -x := abs_of_nonpos h2
    simp only [tri, habs]
    rw [max_eq_left (by linarith)]
    push_cast; ring
  rw [hcong, intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hasDerivAt_primitive_left c hc x)
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  push_cast
  simp only [Complex.exp_zero, mul_zero]
  field_simp
  ring

lemma integral_tri_exp_right (c : ℂ) (hc : c ≠ 0) :
    (∫ v in (0 : ℝ)..1, Complex.exp (c * v) * tri v)
      = Complex.exp c / c ^ 2 - 1 / c - 1 / c ^ 2 := by
  have hcong : ∫ v in (0 : ℝ)..1, Complex.exp (c * v) * tri v
      = ∫ v in (0 : ℝ)..1, Complex.exp (c * v) * (1 - (v : ℂ)) := by
    refine intervalIntegral.integral_congr ?_
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    obtain ⟨h1, h2⟩ := hx
    have habs : |x| = x := abs_of_nonneg h1
    simp only [tri, habs]
    rw [max_eq_left (by linarith)]
    push_cast; ring
  rw [hcong, intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hasDerivAt_primitive_right c hc x)
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  push_cast
  simp only [Complex.exp_zero, mul_zero]
  field_simp
  ring

lemma integral_tri_exp_split (c : ℂ) :
    ∫ v : ℝ, Complex.exp (c * v) * tri v
      = (∫ v in (-1 : ℝ)..0, Complex.exp (c * v) * tri v)
        + ∫ v in (0 : ℝ)..1, Complex.exp (c * v) * tri v := by
  have h0 : ∫ v : ℝ, Complex.exp (c * v) * tri v
      = ∫ v in Set.Ioc (-1 : ℝ) 1, Complex.exp (c * v) * tri v := by
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero ?_).symm
    intro x hx
    simp only [Set.mem_Ioc, not_and_or, not_lt, not_le] at hx
    have : tri x = 0 := by
      refine tri_eq_zero_of_one_le_abs ?_
      rcases hx with h | h
      · exact le_abs.2 (Or.inr (by linarith))
      · exact le_abs.2 (Or.inl (by linarith))
    simp [this]
  rw [h0, ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
    ← intervalIntegral.integral_add_adjacent_intervals (b := 0)
      (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _)]

/-- The total integral `∫ exp (c x) * tri x` in closed form, for `c ≠ 0`. -/
lemma integral_tri_exp (c : ℂ) (hc : c ≠ 0) :
    ∫ v : ℝ, Complex.exp (c * v) * tri v
      = (Complex.exp c + Complex.exp (-c) - 2) / c ^ 2 := by
  rw [integral_tri_exp_split c, integral_tri_exp_left c hc, integral_tri_exp_right c hc]
  field_simp
  ring

/-- The Fourier transform of the tent function is `(sin (π w) / (π w))²`, for `w ≠ 0`. -/
lemma fourier_tri_of_ne_zero {w : ℝ} (hw : w ≠ 0) :
    𝓕 tri w = ((Real.sin (π * w) / (π * w)) ^ 2 : ℝ) := by
  set t : ℝ := π * w with ht
  have hts : t ≠ 0 := mul_ne_zero Real.pi_ne_zero hw
  set c : ℂ := ((-2 * t : ℝ) : ℂ) * I with hcdef
  have hc : c ≠ 0 := by simp [hcdef, Complex.ext_iff, hts]
  have h1 : 𝓕 tri w = ∫ v : ℝ, Complex.exp (c * v) * tri v := by
    rw [Real.fourier_real_eq_integral_exp_smul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only [smul_eq_mul]
    congr 2
    rw [hcdef, ht]
    push_cast
    ring
  rw [h1, integral_tri_exp c hc, hcdef]
  have hcos : Complex.exp ((-2 * t : ℝ) * I) + Complex.exp (-((-2 * t : ℝ) * I))
      = 2 * (Real.cos (2 * t) : ℂ) := by
    rw [Complex.ofReal_cos, Complex.cos]
    push_cast
    ring_nf
  rw [hcos]
  have h2 : Real.cos (2 * t) = 1 - 2 * Real.sin t ^ 2 := by
    rw [Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq t]
  rw [h2]
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hts
  push_cast
  field_simp
  ring_nf
  simp [Complex.I_sq]

lemma fourier_tri_ae :
    𝓕 tri =ᵐ[volume] fun w : ℝ => (((Real.sin (π * w) / (π * w)) ^ 2 : ℝ) : ℂ) := by
  filter_upwards [Measure.ae_ne volume (0 : ℝ)] with w hw
  exact fourier_tri_of_ne_zero hw

lemma sinc_sq_le (w : ℝ) : (Real.sin (π * w) / (π * w)) ^ 2 ≤ 2 * (1 + w ^ 2)⁻¹ := by
  rcases eq_or_ne w 0 with rfl | hw
  · norm_num
  · have hpos : (0 : ℝ) < 1 + w ^ 2 := by positivity
    set t : ℝ := π * w with ht
    have hts : t ≠ 0 := mul_ne_zero Real.pi_ne_zero hw
    have ht2 : 0 < t ^ 2 := by positivity
    have h1 : Real.sin t ^ 2 ≤ 1 := by nlinarith [Real.neg_one_le_sin t, Real.sin_le_one t]
    have h2 : Real.sin t ^ 2 ≤ t ^ 2 := by
      have h := abs_sin_le_abs (x := t)
      nlinarith [abs_nonneg t, abs_nonneg (Real.sin t), sq_abs t, sq_abs (Real.sin t)]
    have hteq : t ^ 2 = π ^ 2 * w ^ 2 := by rw [ht]; ring
    have hpi : (1 : ℝ) ≤ π ^ 2 := by nlinarith [Real.pi_gt_three]
    have hw2 : w ^ 2 ≤ t ^ 2 := by rw [hteq]; nlinarith [sq_nonneg w]
    have key : (1 + w ^ 2) * Real.sin t ^ 2 ≤ 2 * t ^ 2 := by nlinarith
    rw [div_pow, div_le_iff₀ ht2]
    have heq : 2 * (1 + w ^ 2)⁻¹ * t ^ 2 = 2 * t ^ 2 / (1 + w ^ 2) := by field_simp
    rw [heq, le_div_iff₀ hpos]
    nlinarith

lemma integrable_sinc_pi_sq :
    Integrable (fun w : ℝ => (Real.sin (π * w) / (π * w)) ^ 2) := by
  have hmeas : Measurable (fun w : ℝ => (Real.sin (π * w) / (π * w)) ^ 2) :=
    ((Real.measurable_sin.comp (measurable_const_mul π)).div
      (measurable_const_mul π)).pow_const 2
  refine Integrable.mono (integrable_inv_one_add_sq.const_mul 2) hmeas.aestronglyMeasurable ?_
  filter_upwards with w
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * (1 + w ^ 2)⁻¹)]
  exact sinc_sq_le w

/-- `∫ (sin (π w) / (π w))² dw = 1`: Fourier inversion for the tent function at `0`. -/
lemma integral_sinc_pi_sq : ∫ w : ℝ, (Real.sin (π * w) / (π * w)) ^ 2 = 1 := by
  have hFint : Integrable (𝓕 tri) :=
    integrable_sinc_pi_sq.ofReal.congr fourier_tri_ae.symm
  have h0 : 𝓕⁻ (𝓕 tri) 0 = tri 0 :=
    tri_integrable.fourierInv_fourier_eq hFint tri_continuous.continuousAt
  have h1 : 𝓕⁻ (𝓕 tri) 0 = ∫ w : ℝ, 𝓕 tri w := by
    rw [Real.fourierInv_eq']
    simp
  have h2 : tri 0 = 1 := by simp [tri]
  have h3 : ∫ w : ℝ, 𝓕 tri w = ((∫ w : ℝ, (Real.sin (π * w) / (π * w)) ^ 2 : ℝ) : ℂ) := by
    rw [integral_congr_ae fourier_tri_ae, integral_complex_ofReal]
  rw [h1, h2, h3] at h0
  exact_mod_cast h0

/-- The squared sine kernel `x ↦ (sin x / x)²` is Lebesgue integrable on `ℝ`. -/
theorem integrable_sinc_sq : Integrable (fun x : ℝ => (Real.sin x / x) ^ 2) :=
  (integrable_comp_mul_left_iff (fun x : ℝ => (Real.sin x / x) ^ 2) Real.pi_ne_zero).mp
    integrable_sinc_pi_sq

/-- **The normalization of the sine kernel**: `∫_ℝ (sin x / x)² dx = π`, as a Bochner integral
with respect to the Lebesgue measure `volume` on `ℝ`.

The integrand is understood pointwise as `(sin x / x)^2`; at `x = 0` this evaluates to `0` by the
junk-value convention for division, which does not affect the integral since `{0}` is null (the
integrand agrees a.e. with the continuous function `sinc x ^ 2`). -/
theorem integral_sinc_sq : ∫ x : ℝ, (Real.sin x / x) ^ 2 = π := by
  have hc := Measure.integral_comp_mul_left (fun x : ℝ => (Real.sin x / x) ^ 2) π
  rw [integral_sinc_pi_sq, abs_of_pos (by positivity : (0 : ℝ) < π⁻¹), smul_eq_mul,
    inv_mul_eq_div, eq_div_iff Real.pi_ne_zero, one_mul] at hc
  exact hc.symm

end Zeta23Scaffold

