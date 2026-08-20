import Mathlib
/-!
# Integral Sinc Fourth
Category: C Integral
Target: Zeta23Scaffold.integral_sinc_fourth
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
The proof follows the classical Fourier-analytic route.  Writing `Λ` for the tent function
`Λ x = max (1 - |x|) 0`, an elementary computation gives `𝓕 Λ ξ = (sin (π ξ) / (π ξ))²`.
Fourier inversion then gives `𝓕 ((sin (π ·) / (π ·))²) = Λ`, and the multiplication formula
`∫ 𝓕 f · g = ∫ f · 𝓕 g` yields
`∫ (sin (π ξ) / (π ξ))⁴ dξ = ∫ Λ² = 2/3`.
Rescaling `x = π ξ` produces `∫ (sin x / x)⁴ dx = 2 π / 3`.
-/

open MeasureTheory Real Complex intervalIntegral
open scoped FourierTransform

namespace Zeta23Scaffold

/-! ### The tent function and the squared sinc -/

/-- The tent (triangle) function `x ↦ max (1 - |x|) 0`. -/
noncomputable def tent (x : ℝ) : ℝ := max (1 - |x|) 0

/-- The complex-valued tent function. -/
noncomputable def tentC (x : ℝ) : ℂ := (tent x : ℂ)

/-- The square of the normalized sinc function, `ξ ↦ (sin (π ξ) / (π ξ))²`. -/
noncomputable def sincSq (ξ : ℝ) : ℝ := Real.sinc (π * ξ) ^ 2

lemma tent_eq_zero {x : ℝ} (h : 1 ≤ |x|) : tent x = 0 := by
  simp only [tent, max_eq_right_iff]
  linarith

lemma tent_neg (x : ℝ) : tent (-x) = tent x := by simp [tent]

lemma tent_neg_side {x : ℝ} (h : x ∈ Set.uIcc (-1:ℝ) 0) : tent x = 1 + x := by
  rw [Set.uIcc_of_le (by norm_num)] at h
  obtain ⟨h1, h2⟩ := h
  rw [tent, abs_of_nonpos h2, max_eq_left (by linarith)]
  ring

lemma tent_pos_side {x : ℝ} (h : x ∈ Set.uIcc (0:ℝ) 1) : tent x = 1 - x := by
  rw [Set.uIcc_of_le (by norm_num)] at h
  obtain ⟨h1, h2⟩ := h
  rw [tent, abs_of_nonneg h1, max_eq_left (by linarith)]

lemma tent_continuous : Continuous tent := by
  unfold tent; fun_prop

lemma tentC_continuous : Continuous tentC := by
  unfold tentC tent; fun_prop

lemma one_le_abs_of_notMem_Icc {x : ℝ} (hx : x < -1 ∨ 1 < x) : 1 ≤ |x| := by
  rcases hx with hx | hx
  · rw [abs_of_nonpos (by linarith)]; linarith
  · rw [abs_of_nonneg (by linarith)]; linarith

/-- A function vanishing outside `[-1, 1]` has integral equal to the interval integral. -/
lemma integral_eq_interval {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (h : ∀ x, 1 ≤ |x| → f x = 0) :
    ∫ x, f x = ∫ x in (-1:ℝ)..1, f x := by
  rw [intervalIntegral.integral_of_le (by norm_num),
      setIntegral_eq_integral_of_forall_compl_eq_zero]
  intro x hx
  apply h
  simp only [Set.mem_Ioc, not_and_or, not_lt, not_le] at hx
  rcases hx with hx | hx
  · rw [abs_of_nonpos (by linarith)]; linarith
  · rw [abs_of_nonneg (by linarith)]; linarith

lemma tentC_integrable : Integrable tentC := by
  apply Continuous.integrable_of_hasCompactSupport tentC_continuous
  apply HasCompactSupport.intro (isCompact_Icc (a := (-1:ℝ)) (b := 1))
  intro x hx
  simp only [Set.mem_Icc, not_and_or, not_le] at hx
  simp only [tentC, tent_eq_zero (one_le_abs_of_notMem_Icc hx), Complex.ofReal_zero]

lemma integral_tent : ∫ x : ℝ, tent x = 1 := by
  have e1 : ∫ x in (-1:ℝ)..0, tent x = ∫ x in (-1:ℝ)..0, (1 + x) :=
    intervalIntegral.integral_congr (fun x hx => tent_neg_side hx)
  have e2 : ∫ x in (0:ℝ)..1, tent x = ∫ x in (0:ℝ)..1, (1 - x) :=
    intervalIntegral.integral_congr (fun x hx => tent_pos_side hx)
  rw [integral_eq_interval _ (fun x hx => tent_eq_zero hx),
      ← intervalIntegral.integral_add_adjacent_intervals (b := (0:ℝ))
        (tent_continuous.intervalIntegrable _ _) (tent_continuous.intervalIntegrable _ _),
      e1, e2,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x : ℝ => x + x^2/2)
        (fun x _ => by simpa using ((hasDerivAt_id x).add ((hasDerivAt_pow 2 x).div_const 2)))
        (by apply Continuous.intervalIntegrable; fun_prop),
      intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x : ℝ => x - x^2/2)
        (fun x _ => by simpa using ((hasDerivAt_id x).sub ((hasDerivAt_pow 2 x).div_const 2)))
        (by apply Continuous.intervalIntegrable; fun_prop)]
  norm_num

lemma integral_tent_sq : ∫ x : ℝ, tent x ^ 2 = 2/3 := by
  have e1 : ∫ x in (-1:ℝ)..0, tent x ^ 2 = ∫ x in (-1:ℝ)..0, (1 + x)^2 :=
    intervalIntegral.integral_congr (fun x hx => by rw [tent_neg_side hx])
  have e2 : ∫ x in (0:ℝ)..1, tent x ^ 2 = ∫ x in (0:ℝ)..1, (1 - x)^2 :=
    intervalIntegral.integral_congr (fun x hx => by rw [tent_pos_side hx])
  rw [integral_eq_interval _ (fun x hx => by rw [tent_eq_zero hx]; ring),
      ← intervalIntegral.integral_add_adjacent_intervals (b := (0:ℝ))
        ((tent_continuous.pow 2).intervalIntegrable _ _)
        ((tent_continuous.pow 2).intervalIntegrable _ _),
      e1, e2,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x : ℝ => (1+x)^3/3)
        (fun x _ => by simpa using (((hasDerivAt_id x).const_add 1).pow 3).div_const 3)
        (by apply Continuous.intervalIntegrable; fun_prop),
      intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x : ℝ => -(1-x)^3/3)
        (fun x _ => by
          simpa using ((((hasDerivAt_id x).const_sub 1).pow 3).neg).div_const 3)
        (by apply Continuous.intervalIntegrable; fun_prop)]
  norm_num

/-! ### The elementary derivative computations -/

lemma hasDerivAt_cexp_lin (c : ℂ) (v : ℝ) :
    HasDerivAt (fun v : ℝ => Complex.exp (c * v)) (c * Complex.exp (c * v)) v := by
  have hofr : HasDerivAt (fun v : ℝ => (v : ℂ)) 1 v := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := v))
  have h1 : HasDerivAt (fun v : ℝ => (c * (v : ℂ))) c v := by simpa using hofr.const_mul c
  simpa [mul_comm] using h1.cexp

lemma hasDerivAt_G (c : ℂ) (hc : c ≠ 0) (v : ℝ) :
    HasDerivAt (fun v : ℝ => Complex.exp (c * v) * ((1 + (v : ℂ))/c - 1/c^2))
      (Complex.exp (c * v) * (1 + (v : ℂ))) v := by
  have hofr : HasDerivAt (fun v : ℝ => (v : ℂ)) 1 v := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := v))
  have h2 : HasDerivAt (fun v : ℝ => ((1 + (v : ℂ))/c - 1/c^2)) (1/c) v := by
    simpa using ((hofr.const_add 1).div_const c).sub_const (1/c^2)
  have h := (hasDerivAt_cexp_lin c v).mul h2
  convert h using 1
  field_simp
  ring

lemma hasDerivAt_F (c : ℂ) (hc : c ≠ 0) (v : ℝ) :
    HasDerivAt (fun v : ℝ => Complex.exp (c * v) * ((1 - (v : ℂ))/c + 1/c^2))
      (Complex.exp (c * v) * (1 - (v : ℂ))) v := by
  have hofr : HasDerivAt (fun v : ℝ => (v : ℂ)) 1 v := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := v))
  have h2 : HasDerivAt (fun v : ℝ => ((1 - (v : ℂ))/c + 1/c^2)) (-(1/c)) v := by
    have h := ((hofr.const_sub 1).div_const c).add_const (1/c^2)
    convert h using 1
    field_simp
  have h := (hasDerivAt_cexp_lin c v).mul h2
  convert h using 1
  field_simp
  ring

/-- The basic integral `∫ e^{cv} Λ(v) dv = (e^c + e^{-c} - 2)/c²` for `c ≠ 0`. -/
lemma tent_fourier_aux (c : ℂ) (hc : c ≠ 0) :
    ∫ v : ℝ, Complex.exp (c * v) * tentC v
      = (Complex.exp c + Complex.exp (-c) - 2)/c^2 := by
  have hcont : Continuous (fun v : ℝ => Complex.exp (c * v) * tentC v) := by
    have := tentC_continuous; fun_prop
  have e1 : ∫ x in (-1:ℝ)..0, Complex.exp (c * x) * tentC x
      = ∫ x in (-1:ℝ)..0, Complex.exp (c * x) * (1 + (x : ℂ)) :=
    intervalIntegral.integral_congr
      (fun x hx => by simp only [tentC, tent_neg_side hx]; push_cast; ring)
  have e2 : ∫ x in (0:ℝ)..1, Complex.exp (c * x) * tentC x
      = ∫ x in (0:ℝ)..1, Complex.exp (c * x) * (1 - (x : ℂ)) :=
    intervalIntegral.integral_congr
      (fun x hx => by simp only [tentC, tent_pos_side hx]; push_cast; ring)
  have e3 : ∫ x in (-1:ℝ)..0, Complex.exp (c * x) * (1 + (x : ℂ))
      = Complex.exp (c * (0:ℝ)) * ((1 + ((0:ℝ) : ℂ))/c - 1/c^2)
        - Complex.exp (c * ((-1:ℝ) : ℂ)) * ((1 + ((-1:ℝ) : ℂ))/c - 1/c^2) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => hasDerivAt_G c hc v)
      (by apply Continuous.intervalIntegrable; fun_prop)
  have e4 : ∫ x in (0:ℝ)..1, Complex.exp (c * x) * (1 - (x : ℂ))
      = Complex.exp (c * ((1:ℝ) : ℂ)) * ((1 - ((1:ℝ) : ℂ))/c + 1/c^2)
        - Complex.exp (c * ((0:ℝ) : ℂ)) * ((1 - ((0:ℝ) : ℂ))/c + 1/c^2) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => hasDerivAt_F c hc v)
      (by apply Continuous.intervalIntegrable; fun_prop)
  rw [integral_eq_interval _ (fun x hx => by simp [tentC, tent_eq_zero hx]),
      ← intervalIntegral.integral_add_adjacent_intervals (b := (0:ℝ))
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _), e1, e2, e3, e4]
  push_cast
  simp only [Complex.exp_zero, mul_zero, mul_one]
  field_simp
  ring

/-- The Fourier transform of the tent function is the squared normalized sinc. -/
lemma fourier_tentC : 𝓕 tentC = fun ξ : ℝ => (sincSq ξ : ℂ) := by
  funext ξ
  rw [Real.fourier_real_eq_integral_exp_smul]
  rcases eq_or_ne ξ 0 with rfl | hξ
  · have h0 : ∀ v : ℝ, Complex.exp ((↑(-2 * π * v * 0)) * I) • tentC v = tentC v := by
      intro v; norm_num
    simp only [h0]
    rw [show (fun v : ℝ => tentC v) = (fun v : ℝ => ((tent v : ℝ) : ℂ)) from rfl,
      integral_complex_ofReal, integral_tent]
    simp [sincSq]
  · set t : ℝ := π * ξ with ht
    have htne : t ≠ 0 := mul_ne_zero Real.pi_ne_zero hξ
    have hc : ((-2*t : ℝ) : ℂ) * I ≠ 0 :=
      mul_ne_zero (Complex.ofReal_ne_zero.2 (by intro h; exact htne (by linarith)))
        Complex.I_ne_zero
    have hint : (fun v : ℝ => Complex.exp ((↑(-2 * π * v * ξ)) * I) • tentC v)
        = fun v : ℝ => Complex.exp ((((-2*t : ℝ)) : ℂ) * I * v) * tentC v := by
      funext v
      rw [smul_eq_mul]
      congr 2
      push_cast [ht]
      ring
    rw [hint, tent_fourier_aux _ hc]
    have h1 : Complex.exp (((-2*t : ℝ) : ℂ) * I) + Complex.exp (-(((-2*t : ℝ) : ℂ) * I)) - 2
        = ((-4 * Real.sin t ^ 2 : ℝ) : ℂ) := by
      rw [show -(((-2*t : ℝ) : ℂ) * I) = ((2*t : ℝ) : ℂ) * I by push_cast; ring,
        Complex.exp_mul_I, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
        ← Complex.ofReal_cos, ← Complex.ofReal_sin]
      have hcos : Real.cos (-2*t) = Real.cos (2*t) := by
        rw [show (-2*t) = -(2*t) by ring, Real.cos_neg]
      have hsin : Real.sin (-2*t) = -Real.sin (2*t) := by
        rw [show (-2*t) = -(2*t) by ring, Real.sin_neg]
      have hdouble : Real.cos (2*t) = 1 - 2 * Real.sin t ^ 2 := by
        have := Real.sin_sq_add_cos_sq t
        rw [Real.cos_two_mul']
        nlinarith
      rw [hcos, hsin, hdouble]
      push_cast
      ring
    have h2 : (((-2*t : ℝ) : ℂ) * I)^2 = ((-4*t^2 : ℝ) : ℂ) := by
      push_cast
      rw [mul_pow, Complex.I_sq]
      ring
    rw [h1, h2, ← Complex.ofReal_div]
    congr 1
    rw [sincSq, ← ht, Real.sinc_of_ne_zero htne, div_pow]
    field_simp

/-! ### Integrability of the squared sinc -/

lemma sinc_sq_le (t : ℝ) : Real.sinc t ^ 2 ≤ 2 * (1 + t^2)⁻¹ := by
  have hpos : (0:ℝ) < 1 + t^2 := by positivity
  rcases eq_or_ne t 0 with rfl | ht
  · norm_num
  · rw [Real.sinc_of_ne_zero ht, div_pow]
    have h1 : Real.sin t ^ 2 ≤ t^2 := by
      have := Real.abs_sin_le_abs (x := t)
      nlinarith [abs_nonneg (Real.sin t), abs_nonneg t, sq_abs (Real.sin t), sq_abs t]
    have h2 : Real.sin t ^ 2 ≤ 1 := by
      nlinarith [Real.sin_sq_add_cos_sq t, sq_nonneg (Real.cos t)]
    have ht2 : (0:ℝ) < t^2 := by positivity
    have heq : 2 * (1 + t^2)⁻¹ = (2*t^2)/(1+t^2)/t^2 := by field_simp
    rw [heq, div_le_div_iff_of_pos_right ht2, le_div_iff₀ hpos]
    nlinarith

lemma sincSq_nonneg (ξ : ℝ) : 0 ≤ sincSq ξ := sq_nonneg _

lemma sincSq_continuous : Continuous sincSq := by
  unfold sincSq
  exact (Real.continuous_sinc.comp (by fun_prop)).pow 2

lemma sincSqC_integrable : Integrable (fun ξ : ℝ => (sincSq ξ : ℂ)) := by
  have hg : Integrable (fun ξ : ℝ => 2 * (1 + (π*ξ)^2)⁻¹) := by
    apply Integrable.const_mul
    exact (integrable_comp_mul_left_iff (fun x : ℝ => (1+x^2)⁻¹) Real.pi_ne_zero).2
      integrable_inv_one_add_sq
  apply Integrable.mono' hg
  · exact (Complex.continuous_ofReal.comp sincSq_continuous).aestronglyMeasurable
  · filter_upwards with ξ
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sincSq_nonneg ξ)]
    exact sinc_sq_le _

/-- The Fourier transform of the squared sinc is the tent function (Fourier inversion). -/
lemma fourier_sincSqC : (𝓕 fun ξ : ℝ => (sincSq ξ : ℂ)) = tentC := by
  have hinv : 𝓕⁻ (𝓕 tentC) = tentC :=
    Continuous.fourierInv_fourier_eq tentC_continuous tentC_integrable
      (by rw [fourier_tentC]; exact sincSqC_integrable)
  funext x
  rw [← fourier_tentC]
  have hx := Real.fourierInv_eq_fourier_neg (𝓕 tentC) (-x)
  rw [neg_neg] at hx
  rw [← hx, hinv]
  simp [tentC, tent_neg]

/-! ### The Plancherel-type multiplication formula -/

lemma integral_fourier_mul (f g : ℝ → ℂ) (hf : Integrable f) (hg : Integrable g) :
    ∫ ξ : ℝ, 𝓕 f ξ * g ξ = ∫ x : ℝ, f x * 𝓕 g x := by
  have hflip : (innerₗ ℝ).flip = innerₗ ℝ := by
    apply LinearMap.ext; intro x; apply LinearMap.ext; intro y
    exact real_inner_comm x y
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ ℝ) (μ := volume)
    (ν := volume) Real.continuous_fourierChar continuous_inner hf hg
  rw [hflip] at h
  simpa [smul_eq_mul] using h

lemma integral_sincSq_sq : ∫ ξ : ℝ, sincSq ξ ^ 2 = 2/3 := by
  have h := integral_fourier_mul tentC (fun ξ : ℝ => (sincSq ξ : ℂ))
    tentC_integrable sincSqC_integrable
  rw [fourier_tentC, fourier_sincSqC] at h
  have hL : ∫ ξ : ℝ, ((sincSq ξ : ℂ) * (sincSq ξ : ℂ))
      = ((∫ ξ : ℝ, sincSq ξ ^ 2 : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    congr 1
    funext ξ
    push_cast
    ring
  have hR : ∫ x : ℝ, (tentC x * tentC x) = ((∫ x : ℝ, tent x ^ 2 : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    congr 1
    funext x
    simp only [tentC]
    push_cast
    ring
  rw [hL, hR, integral_tent_sq] at h
  exact_mod_cast h

/-! ### The main theorem -/

/-- **The fourth-power sinc integral**: `∫_ℝ (sin x / x)⁴ dx = 2π/3`. -/
theorem integral_sinc_fourth : ∫ x : ℝ, (Real.sin x / x)^4 = 2 * Real.pi / 3 := by
  have h : ∫ x : ℝ, Real.sinc (π * x) ^ 4 = 2/3 := by
    rw [← integral_sincSq_sq]
    congr 1
    funext ξ
    rw [sincSq, ← pow_mul]
  rw [Measure.integral_comp_mul_left (fun y : ℝ => Real.sinc y ^ 4) π,
    smul_eq_mul, abs_of_pos (by positivity)] at h
  have hsinc : ∫ x : ℝ, Real.sinc x ^ 4 = ∫ x : ℝ, (Real.sin x / x)^4 := by
    apply MeasureTheory.integral_congr_ae
    have hae : {(0:ℝ)}ᶜ ∈ ae (volume : Measure ℝ) := by
      rw [mem_ae_iff]; simp
    filter_upwards [hae] with x hx
    rw [Real.sinc_of_ne_zero hx]
  rw [hsinc] at h
  set I : ℝ := ∫ x : ℝ, (Real.sin x / x)^4 with hI
  have hpi : (π:ℝ) ≠ 0 := Real.pi_ne_zero
  field_simp at h
  linarith

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

