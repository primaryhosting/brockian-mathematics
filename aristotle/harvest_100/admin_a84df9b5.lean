import Mathlib

/-!
# Integral Sinc Sq
Category: C Integral
Target: Zeta23Scaffold.integral_sinc_sq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Complex Filter intervalIntegral
open scoped FourierTransform Topology Real

namespace Zeta23Scaffold

/-- The triangle ("tent") function `x ↦ max 0 (1 - |x|)`, viewed as a complex-valued function. -/
noncomputable def tri (x : ℝ) : ℂ := ((max 0 (1 - |x|) : ℝ) : ℂ)

lemma continuous_tri : Continuous tri := by
  unfold tri
  fun_prop

lemma tri_eq_zero {x : ℝ} (hx : 1 ≤ |x|) : tri x = 0 := by
  simp only [tri, Complex.ofReal_eq_zero]
  exact max_eq_left (by linarith)

lemma tri_zero : tri 0 = 1 := by
  simp [tri]

lemma hasCompactSupport_tri : HasCompactSupport tri := by
  apply HasCompactSupport.intro (isCompact_Icc (a := (-1 : ℝ)) (b := 1))
  intro x hx
  apply tri_eq_zero
  simp only [Set.mem_Icc, not_and_or, not_le] at hx
  rcases hx with h | h
  · rw [abs_of_nonpos (by linarith)]; linarith
  · rw [abs_of_nonneg (by linarith)]; linarith

lemma integrable_tri : Integrable tri :=
  continuous_tri.integrable_of_hasCompactSupport hasCompactSupport_tri

/-- The explicit antiderivative computation: the integral of the tent function against
a complex exponential `exp (k x)`. -/
lemma tri_interval (k : ℂ) (hk : k ≠ 0) :
    ∫ x in (-1:ℝ)..1, ((1 - |x| : ℝ) : ℂ) * Complex.exp (k * x)
      = (Complex.exp k + Complex.exp (-k) - 2) / k ^ 2 := by
  have hd1 : ∀ x : ℝ, HasDerivAt
      (fun y : ℝ => ((1 - (y:ℂ))/k) * Complex.exp (k*y) + Complex.exp (k*y)/k^2)
      ((1 - (x:ℂ)) * Complex.exp (k*x)) x := by
    intro x
    have h0 : HasDerivAt (fun y : ℝ => (y:ℂ)) 1 x := Complex.ofRealCLM.hasDerivAt
    have h1 : HasDerivAt (fun y : ℝ => Complex.exp (k*y)) (Complex.exp (k*x) * (k*1)) x :=
      (h0.const_mul k).cexp
    have h2 := ((((h0.const_sub 1).div_const k).mul h1).add (h1.div_const (k^2)))
    convert h2 using 1
    field_simp
    ring
  have hd2 : ∀ x : ℝ, HasDerivAt
      (fun y : ℝ => ((1 + (y:ℂ))/k) * Complex.exp (k*y) - Complex.exp (k*y)/k^2)
      ((1 + (x:ℂ)) * Complex.exp (k*x)) x := by
    intro x
    have h0 : HasDerivAt (fun y : ℝ => (y:ℂ)) 1 x := Complex.ofRealCLM.hasDerivAt
    have h1 : HasDerivAt (fun y : ℝ => Complex.exp (k*y)) (Complex.exp (k*x) * (k*1)) x :=
      (h0.const_mul k).cexp
    have h2 := ((((h0.const_add 1).div_const k).mul h1).sub (h1.div_const (k^2)))
    convert h2 using 1
    field_simp
    ring
  have ii1 : IntervalIntegrable (fun x : ℝ => (1 - (x:ℂ)) * Complex.exp (k*x)) volume 0 1 :=
    (by fun_prop : Continuous fun x : ℝ => (1 - (x:ℂ)) * Complex.exp (k*x)).intervalIntegrable 0 1
  have ii2 : IntervalIntegrable (fun x : ℝ => (1 + (x:ℂ)) * Complex.exp (k*x)) volume (-1) 0 :=
    (by fun_prop :
      Continuous fun x : ℝ => (1 + (x:ℂ)) * Complex.exp (k*x)).intervalIntegrable (-1) 0
  have e1 : ∫ x in (0:ℝ)..1, (1 - (x:ℂ)) * Complex.exp (k*x)
      = Complex.exp k/k^2 - 1/k - 1/k^2 := by
    rw [integral_eq_sub_of_hasDerivAt (fun x _ => hd1 x) ii1]
    push_cast
    simp only [mul_zero, Complex.exp_zero, mul_one]
    field_simp
    ring
  have e2 : ∫ x in (-1:ℝ)..0, (1 + (x:ℂ)) * Complex.exp (k*x)
      = 1/k - 1/k^2 + Complex.exp (-k)/k^2 := by
    rw [integral_eq_sub_of_hasDerivAt (fun x _ => hd2 x) ii2]
    push_cast
    simp only [mul_zero, Complex.exp_zero, mul_one]
    field_simp
    ring
  have c1 : (∫ x in (0:ℝ)..1, ((1 - |x| : ℝ):ℂ) * Complex.exp (k*x))
      = ∫ x in (0:ℝ)..1, (1 - (x:ℂ)) * Complex.exp (k*x) := by
    apply integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hx
    simp [abs_of_nonneg hx.1]
  have c2 : (∫ x in (-1:ℝ)..0, ((1 - |x| : ℝ):ℂ) * Complex.exp (k*x))
      = ∫ x in (-1:ℝ)..0, (1 + (x:ℂ)) * Complex.exp (k*x) := by
    apply integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (-1:ℝ) ≤ 0)] at hx
    simp [abs_of_nonpos hx.2]
  have hsplit : (∫ x in (-1:ℝ)..1, ((1 - |x| : ℝ):ℂ) * Complex.exp (k*x))
      = (∫ x in (-1:ℝ)..0, ((1 - |x| : ℝ):ℂ) * Complex.exp (k*x))
        + ∫ x in (0:ℝ)..1, ((1 - |x| : ℝ):ℂ) * Complex.exp (k*x) := by
    rw [integral_add_adjacent_intervals]
    · apply Continuous.intervalIntegrable; fun_prop
    · apply Continuous.intervalIntegrable; fun_prop
  rw [hsplit, c1, c2, e1, e2]
  field_simp
  ring

/-- The Fourier transform of the tent function is `(sin (π ξ) / (π ξ))²`. -/
lemma fourier_tri {ξ : ℝ} (hξ : ξ ≠ 0) :
    𝓕 tri ξ = ((Real.sin (π * ξ) / (π * ξ)) ^ 2 : ℝ) := by
  set k : ℂ := ((-2 * π * ξ : ℝ) : ℂ) * Complex.I with hk
  have hkne : k ≠ 0 := by
    simp [hk, Complex.ext_iff, Real.pi_ne_zero, hξ]
  have step1 : 𝓕 tri ξ = ∫ v : ℝ, Complex.exp (k * v) • tri v := by
    rw [Real.fourier_real_eq_integral_exp_smul]
    congr 1
    ext v
    congr 2
    rw [hk]
    push_cast
    ring
  have step2 : (∫ v : ℝ, Complex.exp (k * v) • tri v)
      = ∫ v in Set.Ioc (-1:ℝ) 1, Complex.exp (k * v) • tri v := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro x hx
    simp only [Set.mem_Ioc, not_and_or, not_lt, not_le] at hx
    rw [tri_eq_zero ?_, smul_zero]
    rcases hx with h | h
    · rw [abs_of_nonpos (by linarith)]; linarith
    · rw [abs_of_nonneg (by linarith)]; linarith
  have step3 : (∫ v in Set.Ioc (-1:ℝ) 1, Complex.exp (k * v) • tri v)
      = ∫ v in (-1:ℝ)..1, ((1 - |v| : ℝ) : ℂ) * Complex.exp (k * v) := by
    rw [integral_of_le (by norm_num : (-1:ℝ) ≤ 1)]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro v hv
    simp only [Set.mem_Ioc] at hv
    have hv' : |v| ≤ 1 := abs_le.2 ⟨hv.1.le, hv.2⟩
    simp only [tri, smul_eq_mul, max_eq_right (by linarith : (0:ℝ) ≤ 1 - |v|)]
    ring
  rw [step1, step2, step3, tri_interval k hkne]
  have hcos : Complex.exp k + Complex.exp (-k) = 2 * ((Real.cos (2*π*ξ) : ℝ) : ℂ) := by
    rw [hk, Complex.exp_mul_I, ← neg_mul, Complex.exp_mul_I]
    push_cast
    simp only [Complex.cos_neg, Complex.sin_neg]
    rw [show ((-2 * (π:ℂ) * ξ)) = -(2*(π:ℂ)*ξ) by ring]
    simp [Complex.cos_neg, Complex.sin_neg]
    ring
  have hk2 : k^2 = -(((2*π*ξ)^2 : ℝ) : ℂ) := by
    rw [hk]
    push_cast
    rw [mul_pow, Complex.I_sq]
    ring
  rw [hcos, hk2]
  have hπξ : (π * ξ) ≠ 0 := mul_ne_zero Real.pi_ne_zero hξ
  have hreal : (Real.sin (π * ξ) / (π * ξ)) ^ 2 * (-((2*π*ξ)^2)) = 2 * Real.cos (2*π*ξ) - 2 := by
    have hcc : Real.cos (2*π*ξ) = 1 - 2*Real.sin (π*ξ)^2 := by
      rw [show 2*π*ξ = 2*(π*ξ) by ring, Real.cos_two_mul, Real.cos_sq']
      ring
    rw [hcc]
    field_simp
    ring
  have hne : (-(((2*π*ξ)^2 : ℝ) : ℂ)) ≠ 0 := by
    simp only [ne_eq, neg_eq_zero, Complex.ofReal_eq_zero]
    intro h
    exact hπξ (by nlinarith [h])
  rw [div_eq_iff hne]
  exact_mod_cast hreal.symm

/-- The (continuous) function `sinc²` is integrable on `ℝ`. -/
lemma integrable_sincSq : Integrable (fun x : ℝ => (Real.sinc x) ^ 2) := by
  apply Integrable.mono' (integrable_inv_one_add_sq.const_mul 2)
  · exact (Real.continuous_sinc.pow 2).aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h1 : Real.sinc x ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one _).2 (Real.abs_sinc_le_one x)
    have hp : (0:ℝ) < 1 + x^2 := by positivity
    rcases le_or_gt (x^2) 1 with h | h
    · rw [← div_eq_mul_inv, le_div_iff₀ hp]
      nlinarith
    · have hx2 : (0:ℝ) < x^2 := by linarith
      have h2 : Real.sinc x ^ 2 ≤ 1 / x^2 := by
        have hx : x ≠ 0 := by intro h0; rw [h0] at hx2; simp at hx2
        rw [Real.sinc_of_ne_zero hx, div_pow]
        gcongr
        exact Real.sin_sq_le_one x
      refine h2.trans ?_
      rw [← div_eq_mul_inv, div_le_div_iff₀ hx2 hp]
      nlinarith

lemma sinSq_div_sq_ae_eq_sincSq :
    (fun x : ℝ => (Real.sin x / x) ^ 2) =ᵐ[volume] fun x : ℝ => (Real.sinc x) ^ 2 := by
  have h0 : ({(0:ℝ)}ᶜ : Set ℝ) ∈ ae (volume : Measure ℝ) := by
    simp [MeasureTheory.compl_mem_ae_iff]
  filter_upwards [h0] with x hx
  rw [Real.sinc_of_ne_zero hx]

/-- `(sin x / x)²` is integrable on `ℝ`. -/
lemma integrable_sinSq_div_sq : Integrable (fun x : ℝ => (Real.sin x / x) ^ 2) :=
  integrable_sincSq.congr sinSq_div_sq_ae_eq_sincSq.symm

lemma integrable_scaled : Integrable (fun ξ : ℝ => (Real.sin (π * ξ) / (π * ξ)) ^ 2) :=
  integrable_sinSq_div_sq.comp_mul_left' Real.pi_ne_zero

lemma fourier_tri_ae :
    𝓕 tri =ᵐ[volume] fun ξ : ℝ => (((Real.sin (π * ξ) / (π * ξ)) ^ 2 : ℝ) : ℂ) := by
  have h0 : ({(0:ℝ)}ᶜ : Set ℝ) ∈ ae (volume : Measure ℝ) := by
    simp [MeasureTheory.compl_mem_ae_iff]
  filter_upwards [h0] with ξ hξ
  exact fourier_tri hξ

lemma integrable_fourier_tri : Integrable (𝓕 tri) :=
  (integrable_scaled.ofReal (𝕜 := ℂ)).congr fourier_tri_ae.symm

lemma integral_fourier_tri : ∫ ξ : ℝ, 𝓕 tri ξ = 1 := by
  have h := integrable_tri.fourierInv_fourier_eq integrable_fourier_tri
    (v := (0:ℝ)) continuous_tri.continuousAt
  rw [Real.fourierInv_eq'] at h
  simpa [tri_zero] using h

/-- **The normalization integral of the sine kernel**:
`∫_ℝ (sin x / x)² dx = π`.  (At `x = 0` the integrand is `0/0 = 0` in Lean, which does not
affect the value of the integral, since the integrand agrees almost everywhere with the
continuous function `sinc²`.) -/
theorem integral_sinc_sq : ∫ x : ℝ, (Real.sin x / x) ^ 2 = π := by
  have h1 : ∫ ξ : ℝ, 𝓕 tri ξ = ((∫ ξ : ℝ, (Real.sin (π * ξ) / (π * ξ)) ^ 2 : ℝ) : ℂ) := by
    rw [integral_congr_ae fourier_tri_ae, integral_complex_ofReal]
  have h2 : (∫ ξ : ℝ, (Real.sin (π * ξ) / (π * ξ)) ^ 2) = 1 := by
    have := integral_fourier_tri
    rw [h1] at this
    exact_mod_cast this
  have h3 : (∫ ξ : ℝ, (Real.sin (π * ξ) / (π * ξ)) ^ 2)
      = |π⁻¹| • ∫ x : ℝ, (Real.sin x / x) ^ 2 :=
    Measure.integral_comp_mul_left (fun y : ℝ => (Real.sin y / y) ^ 2) π
  rw [h2, abs_of_pos (by positivity : (0:ℝ) < π⁻¹), smul_eq_mul] at h3
  have h4 : π * 1 = π * (π⁻¹ * ∫ x : ℝ, (Real.sin x / x) ^ 2) := by rw [← h3]
  rw [mul_one, ← mul_assoc, mul_inv_cancel₀ Real.pi_ne_zero, one_mul] at h4
  exact h4.symm

/-- The same integral written with Mathlib's continuous `Real.sinc` function. -/
theorem integral_sinc_sq' : ∫ x : ℝ, (Real.sinc x) ^ 2 = π := by
  rw [← integral_congr_ae sinSq_div_sq_ae_eq_sincSq]
  exact integral_sinc_sq

/-- Normalized form of the sine-kernel normalization integral:
`∫_ℝ S(u)² du = 1` for `S(u) = sin (π u) / (π u)`. -/
theorem integral_sine_kernel_sq : ∫ u : ℝ, (Real.sin (π * u) / (π * u)) ^ 2 = 1 := by
  rw [Measure.integral_comp_mul_left (fun y : ℝ => (Real.sin y / y) ^ 2) π,
    integral_sinc_sq, abs_of_pos (by positivity : (0:ℝ) < π⁻¹), smul_eq_mul,
    inv_mul_cancel₀ Real.pi_ne_zero]

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

