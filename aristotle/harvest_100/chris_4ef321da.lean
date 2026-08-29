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
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Zeta23Scaffold

open scoped FourierTransform
open MeasureTheory Real Complex

/-! ## The tent function and its Fourier transform -/

/-- The tent (triangle) function, supported on `[-1,1]`. -/
noncomputable def tent (x : ℝ) : ℝ := max (1 - |x|) 0

/-- The tent function viewed as a complex-valued function. -/
noncomputable def tentC (x : ℝ) : ℂ := (tent x : ℂ)

lemma tent_neg (x : ℝ) : tent (-x) = tent x := by
  simp [tent]

lemma tent_eq_zero_of_one_le {x : ℝ} (hx : 1 ≤ |x|) : tent x = 0 := by
  simp only [tent]
  exact max_eq_right (by linarith)

lemma tentC_eq_zero_of_one_le {x : ℝ} (hx : 1 ≤ |x|) : tentC x = 0 := by
  simp [tentC, tent_eq_zero_of_one_le hx]

lemma continuous_tent : Continuous tent := by
  unfold tent; fun_prop

lemma continuous_tentC : Continuous tentC :=
  Complex.continuous_ofReal.comp continuous_tent

lemma hasCompactSupport_tentC : HasCompactSupport tentC := by
  apply HasCompactSupport.intro (isCompact_Icc (a := (-1 : ℝ)) (b := 1))
  intro x hx
  apply tentC_eq_zero_of_one_le
  simp only [Set.mem_Icc, not_and_or, not_le] at hx
  rcases hx with h | h
  · rw [abs_of_nonpos (by linarith)]; linarith
  · rw [abs_of_nonneg (by linarith)]; linarith

lemma integrable_tentC : Integrable tentC :=
  continuous_tentC.integrable_of_hasCompactSupport hasCompactSupport_tentC

/-- A function vanishing outside `[-1,1]` has its integral over `ℝ` equal to an interval
integral. -/
lemma integral_eq_intervalIntegral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (hf : ∀ x : ℝ, 1 ≤ |x| → f x = 0) :
    ∫ x : ℝ, f x = ∫ x in (-1 : ℝ)..1, f x := by
  rw [intervalIntegral.integral_of_le (by norm_num),
    ← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (s := Set.Ioc (-1 : ℝ) 1)]
  intro x hx
  apply hf
  simp only [Set.mem_Ioc, not_and_or, not_lt, not_le] at hx
  rcases hx with h | h
  · rw [abs_of_nonpos (by linarith)]; linarith
  · rw [abs_of_nonneg (by linarith)]; linarith

/-- Splitting the interval integral of `g * tentC` into the two linear pieces. -/
lemma intervalIntegral_mul_tentC (g : ℝ → ℂ) (hg : Continuous g) :
    (∫ v in (-1 : ℝ)..1, g v * tentC v)
      = (∫ v in (-1 : ℝ)..0, g v * (1 + (v : ℂ))) + (∫ v in (0 : ℝ)..1, g v * (1 - (v : ℂ))) := by
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := (0 : ℝ))
      (by apply Continuous.intervalIntegrable; exact hg.mul continuous_tentC)
      (by apply Continuous.intervalIntegrable; exact hg.mul continuous_tentC)]
  congr 1
  · apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by norm_num)] at hx
    simp only [Set.mem_Icc] at hx
    have hax : |x| = -x := abs_of_nonpos hx.2
    simp only [tentC, tent, hax]
    rw [max_eq_left (by linarith)]
    push_cast
    ring
  · apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by norm_num)] at hx
    simp only [Set.mem_Icc] at hx
    have hax : |x| = x := abs_of_nonneg hx.1
    simp only [tentC, tent, hax]
    rw [max_eq_left (by linarith)]
    push_cast
    ring

lemma hasDerivAt_cexp_mul (c : ℂ) (v : ℝ) :
    HasDerivAt (fun x : ℝ => Complex.exp (c * (x : ℂ))) (c * Complex.exp (c * v)) v := by
  have h : HasDerivAt (fun x : ℝ => c * (x : ℂ)) c v := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := v)).const_mul c
  simpa [mul_comm] using h.cexp

lemma integral_cexp_mul_one_sub (c : ℂ) (hc : c ≠ 0) :
    (∫ v in (0 : ℝ)..1, Complex.exp (c * v) * (1 - (v : ℂ)))
      = Complex.exp c / c ^ 2 - (1 / c + 1 / c ^ 2) := by
  have key : ∀ v : ℝ, HasDerivAt
      (fun x : ℝ => Complex.exp (c * x) * ((1 - (x : ℂ)) / c + 1 / c ^ 2))
      (Complex.exp (c * v) * (1 - (v : ℂ))) v := by
    intro v
    have h1 := hasDerivAt_cexp_mul c v
    have h2 : HasDerivAt (fun x : ℝ => (1 - (x : ℂ)) / c + 1 / c ^ 2) (-1 / c) v := by
      have h3 : HasDerivAt (fun x : ℝ => (1 - (x : ℂ))) (-1) v := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := v)).const_sub 1
      simpa [div_eq_mul_inv] using (h3.div_const c).add_const (1 / c ^ 2)
    have h4 := h1.mul h2
    convert h4 using 1
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => key v)]
  · simp only [Complex.ofReal_one, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one,
      sub_self, zero_div, zero_add, sub_zero]
    field_simp
  · apply Continuous.intervalIntegrable
    fun_prop

lemma integral_cexp_mul_one_add (c : ℂ) (hc : c ≠ 0) :
    (∫ v in (-1 : ℝ)..0, Complex.exp (c * v) * (1 + (v : ℂ)))
      = 1 / c - 1 / c ^ 2 + Complex.exp (-c) / c ^ 2 := by
  have key : ∀ v : ℝ, HasDerivAt
      (fun x : ℝ => Complex.exp (c * x) * ((1 + (x : ℂ)) / c - 1 / c ^ 2))
      (Complex.exp (c * v) * (1 + (v : ℂ))) v := by
    intro v
    have h1 := hasDerivAt_cexp_mul c v
    have h2 : HasDerivAt (fun x : ℝ => (1 + (x : ℂ)) / c - 1 / c ^ 2) (1 / c) v := by
      have h3 : HasDerivAt (fun x : ℝ => (1 + (x : ℂ))) 1 v := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := v)).const_add 1
      simpa [div_eq_mul_inv] using (h3.div_const c).sub_const (1 / c ^ 2)
    have h4 := h1.mul h2
    convert h4 using 1
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => key v)]
  · simp only [Complex.ofReal_one, Complex.ofReal_zero, mul_zero, Complex.exp_zero,
      Complex.ofReal_neg, add_zero, add_neg_cancel, zero_div]
    rw [show c * (-1 : ℂ) = -c by ring]
    field_simp
    ring
  · apply Continuous.intervalIntegrable
    fun_prop

/-- The Fourier transform of the tent function is `sinc (π ξ) ^ 2`. -/
lemma fourier_tentC (ξ : ℝ) : 𝓕 tentC ξ = ((Real.sinc (π * ξ) ^ 2 : ℝ) : ℂ) := by
  set c : ℂ := ((-2 * π * ξ : ℝ) : ℂ) * I with hcdef
  have hstep : 𝓕 tentC ξ = (∫ v in (-1 : ℝ)..0, Complex.exp (c * v) * (1 + (v : ℂ)))
      + (∫ v in (0 : ℝ)..1, Complex.exp (c * v) * (1 - (v : ℂ))) := by
    rw [Real.fourier_real_eq_integral_exp_smul]
    have hint : ∀ v : ℝ, Complex.exp (((-2 * π * v * ξ : ℝ) : ℂ) * I) • tentC v
        = Complex.exp (c * v) * tentC v := by
      intro v
      rw [smul_eq_mul]
      congr 2
      rw [hcdef]
      push_cast
      ring
    simp_rw [hint]
    rw [integral_eq_intervalIntegral _ (fun x hx => by
      rw [tentC_eq_zero_of_one_le hx, mul_zero])]
    exact intervalIntegral_mul_tentC _ (by fun_prop)
  rcases eq_or_ne ξ 0 with hξ | hξ
  · have hc0 : c = 0 := by rw [hcdef, hξ]; push_cast; ring
    rw [hstep, hc0]
    have e1 : (∫ v in (-1 : ℝ)..0, Complex.exp ((0 : ℂ) * v) * (1 + (v : ℂ)))
        = ((1 / 2 : ℝ) : ℂ) := by
      have : ∀ v : ℝ, Complex.exp ((0 : ℂ) * v) * (1 + (v : ℂ)) = ((1 + v : ℝ) : ℂ) := by
        intro v; push_cast; simp
      rw [intervalIntegral.integral_congr (fun v _ => this v),
        intervalIntegral.integral_ofReal]
      norm_num
      have := intervalIntegral.integral_comp_add_left (a := (-1 : ℝ)) (b := 0)
        (f := fun y : ℝ => y) (d := 1)
      simp only at this
      rw [this]
      norm_num
    have e2 : (∫ v in (0 : ℝ)..1, Complex.exp ((0 : ℂ) * v) * (1 - (v : ℂ)))
        = ((1 / 2 : ℝ) : ℂ) := by
      have : ∀ v : ℝ, Complex.exp ((0 : ℂ) * v) * (1 - (v : ℂ)) = ((1 - v : ℝ) : ℂ) := by
        intro v; push_cast; simp
      rw [intervalIntegral.integral_congr (fun v _ => this v),
        intervalIntegral.integral_ofReal]
      norm_num
      have := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := 1)
        (f := fun y : ℝ => y) (d := 1)
      simp only at this
      rw [this]
      norm_num
    rw [e1, e2, hξ]
    norm_num
  · have hpi : (π : ℝ) ≠ 0 := Real.pi_ne_zero
    have hcne : c ≠ 0 := by
      rw [hcdef]
      apply mul_ne_zero _ Complex.I_ne_zero
      simp only [ne_eq, Complex.ofReal_eq_zero]
      exact mul_ne_zero (mul_ne_zero (by norm_num) hpi) hξ
    rw [hstep, integral_cexp_mul_one_add c hcne, integral_cexp_mul_one_sub c hcne]
    have hS : 1 / c - 1 / c ^ 2 + Complex.exp (-c) / c ^ 2
        + (Complex.exp c / c ^ 2 - (1 / c + 1 / c ^ 2))
        = (Complex.exp c + Complex.exp (-c) - 2) / c ^ 2 := by
      field_simp
      ring
    rw [hS, hcdef]
    -- now the explicit trigonometric computation
    have hne : π * ξ ≠ 0 := mul_ne_zero hpi hξ
    rw [Real.sinc_of_ne_zero hne]
    set θ : ℝ := 2 * π * ξ with hθ
    have hcast : ((-2 * π * ξ : ℝ) : ℂ) = -(θ : ℂ) := by rw [hθ]; push_cast; ring
    have hsum : Complex.exp (((-2 * π * ξ : ℝ) : ℂ) * I)
        + Complex.exp (-(((-2 * π * ξ : ℝ) : ℂ) * I)) = 2 * ((Real.cos θ : ℝ) : ℂ) := by
      rw [hcast, show -(-(θ : ℂ) * I) = (θ : ℂ) * I by ring, Complex.ofReal_cos, Complex.cos]
      ring
    have hden : ((((-2 * π * ξ : ℝ) : ℂ) * I) ^ 2) = -((θ : ℂ) ^ 2) := by
      rw [hcast, mul_pow, Complex.I_sq]; ring
    rw [hsum, hden]
    have hcos : Real.cos θ = 1 - 2 * Real.sin (π * ξ) ^ 2 := by
      have h2 : θ = 2 * (π * ξ) := by rw [hθ]; ring
      rw [h2, Real.cos_two_mul]
      nlinarith [Real.sin_sq_add_cos_sq (π * ξ)]
    rw [hcos]
    have hθ2 : (θ : ℂ) = 2 * (π : ℂ) * (ξ : ℂ) := by rw [hθ]; push_cast; ring
    push_cast
    rw [hθ2]
    have hpic : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hpi
    have hxc : (ξ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hξ
    field_simp
    ring

/-! ## Integrability of `sinc (π ξ) ^ 2` -/

lemma sinc_pi_sq_le (ξ : ℝ) : Real.sinc (π * ξ) ^ 2 ≤ 2 * (1 + ξ ^ 2)⁻¹ := by
  have hpi : (1 : ℝ) ≤ π := by linarith [Real.pi_gt_three]
  have hpos : (0 : ℝ) < 1 + ξ ^ 2 := by positivity
  have hge : ξ ^ 2 ≤ (π * ξ) ^ 2 := by
    have : (0 : ℝ) ≤ ξ ^ 2 * (π ^ 2 - 1) := mul_nonneg (sq_nonneg ξ) (by nlinarith)
    nlinarith
  rcases le_or_gt ((π * ξ) ^ 2) 1 with h | h
  · have hx2 : ξ ^ 2 ≤ 1 := le_trans hge h
    have h1 : Real.sinc (π * ξ) ^ 2 ≤ 1 := by
      nlinarith [Real.abs_sinc_le_one (π * ξ), abs_nonneg (Real.sinc (π * ξ)),
        sq_abs (Real.sinc (π * ξ))]
    have h2 : (1 : ℝ) ≤ 2 * (1 + ξ ^ 2)⁻¹ := by
      rw [le_mul_inv_iff₀ hpos]; linarith
    linarith
  · have hne : π * ξ ≠ 0 := by
      intro h0; rw [h0] at h; norm_num at h
    have hξ : ξ ≠ 0 := by
      intro h0; exact hne (by rw [h0, mul_zero])
    have hsq : Real.sinc (π * ξ) ^ 2 ≤ ((π * ξ) ^ 2)⁻¹ := by
      rw [Real.sinc_of_ne_zero hne, div_pow, div_le_iff₀ (by positivity),
        inv_mul_cancel₀ (by positivity)]
      nlinarith [Real.sin_sq_le_one (π * ξ)]
    have h3 : ((π * ξ) ^ 2)⁻¹ ≤ 2 * (1 + ξ ^ 2)⁻¹ := by
      have heq : 2 * (1 + ξ ^ 2)⁻¹ - ((π * ξ) ^ 2)⁻¹
          = (2 * (π * ξ) ^ 2 - (1 + ξ ^ 2)) / ((1 + ξ ^ 2) * (π * ξ) ^ 2) := by
        have h1 : (1 : ℝ) + ξ ^ 2 ≠ 0 := by positivity
        have h2 : π ≠ 0 := Real.pi_ne_zero
        field_simp
      have hnum : 0 ≤ 2 * (π * ξ) ^ 2 - (1 + ξ ^ 2) := by linarith
      have hfin : 0 ≤ 2 * (1 + ξ ^ 2)⁻¹ - ((π * ξ) ^ 2)⁻¹ := by
        rw [heq]; positivity
      linarith
    linarith

lemma integrable_sincSq : Integrable (fun ξ : ℝ => ((Real.sinc (π * ξ) ^ 2 : ℝ) : ℂ)) := by
  refine MeasureTheory.Integrable.mono' (g := fun ξ : ℝ => 2 * (1 + ξ ^ 2)⁻¹)
    (integrable_inv_one_add_sq.const_mul 2) ?_ ?_
  · exact (Complex.continuous_ofReal.comp (by fun_prop)).aestronglyMeasurable
  · filter_upwards with ξ
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact sinc_pi_sq_le ξ

/-! ## The `L²` norm of the tent function -/

lemma integral_tent_sq : ∫ x : ℝ, (tent x) ^ 2 = 2 / 3 := by
  rw [integral_eq_intervalIntegral (fun x => (tent x) ^ 2)
    (fun x hx => by show tent x ^ 2 = 0; rw [tent_eq_zero_of_one_le hx]; ring)]
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := (0 : ℝ)) (a := -1) (c := 1)
      (by apply Continuous.intervalIntegrable; exact continuous_tent.pow 2)
      (by apply Continuous.intervalIntegrable; exact continuous_tent.pow 2)]
  have h1 : ∫ x in (-1 : ℝ)..0, (tent x) ^ 2 = ∫ x in (-1 : ℝ)..0, (1 + x) ^ 2 := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by norm_num)] at hx
    simp only [Set.mem_Icc] at hx
    have hax : |x| = -x := abs_of_nonpos hx.2
    simp only [tent, hax]
    rw [max_eq_left (by linarith)]
    ring
  have h2 : ∫ x in (0 : ℝ)..1, (tent x) ^ 2 = ∫ x in (0 : ℝ)..1, (1 - x) ^ 2 := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by norm_num)] at hx
    simp only [Set.mem_Icc] at hx
    have hax : |x| = x := abs_of_nonneg hx.1
    simp only [tent, hax]
    rw [max_eq_left (by linarith)]
  rw [h1, h2]
  have e1 : (∫ x in (-1 : ℝ)..0, (1 + x) ^ 2) = 1 / 3 := by
    have := intervalIntegral.integral_comp_add_left (a := (-1 : ℝ)) (b := 0)
      (f := fun y : ℝ => y ^ 2) (d := 1)
    simp only at this
    rw [this]
    norm_num
  have e2 : (∫ x in (0 : ℝ)..1, (1 - x) ^ 2) = 1 / 3 := by
    have := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := 1)
      (f := fun y : ℝ => y ^ 2) (d := 1)
    simp only at this
    rw [this]
    norm_num
  rw [e1, e2]
  norm_num

/-! ## Plancherel step -/

/-- The key Plancherel-type identity: `∫ sinc (π ξ) ^ 4 dξ = 2/3`. -/
lemma integral_sinc_pi_pow_four : ∫ ξ : ℝ, Real.sinc (π * ξ) ^ 4 = 2 / 3 := by
  set g : ℝ → ℂ := fun ξ => ((Real.sinc (π * ξ) ^ 2 : ℝ) : ℂ) with hgdef
  have hFt : 𝓕 tentC = g := funext fourier_tentC
  have hgint : Integrable g := integrable_sincSq
  have hFtint : Integrable (𝓕 tentC) := by rw [hFt]; exact hgint
  have hinv : ∀ x : ℝ, 𝓕 g x = tentC x := by
    intro x
    have h1 : 𝓕⁻ (𝓕 tentC) = tentC :=
      continuous_tentC.fourierInv_fourier_eq integrable_tentC hFtint
    have h2 : 𝓕⁻ (𝓕 tentC) (-x) = 𝓕 (𝓕 tentC) x := by
      rw [fourierInv_eq_fourier_neg, neg_neg]
    rw [← hFt, ← h2, h1]
    simp [tentC, tent_neg]
  have hmul : ∫ ξ : ℝ, 𝓕 tentC ξ * g ξ = ∫ x : ℝ, tentC x * 𝓕 g x := by
    simpa using VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ ℝ)
      (V := ℝ) (W := ℝ) Real.continuous_fourierChar (by fun_prop) integrable_tentC hgint
  rw [hFt] at hmul
  simp_rw [hinv] at hmul
  have hL : ∫ ξ : ℝ, g ξ * g ξ = ((∫ ξ : ℝ, Real.sinc (π * ξ) ^ 4 : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    congr 1
    funext ξ
    rw [hgdef]
    push_cast
    ring
  have hR : ∫ x : ℝ, tentC x * tentC x = ((2 / 3 : ℝ) : ℂ) := by
    rw [← integral_tent_sq, ← integral_complex_ofReal]
    congr 1
    funext x
    simp only [tentC]
    push_cast
    ring
  rw [hL, hR] at hmul
  exact_mod_cast hmul

theorem integral_sinc_fourth : ∫ x : ℝ, (Real.sin x / x) ^ 4 = 2 * Real.pi / 3 := by
  have hc := MeasureTheory.Measure.integral_comp_mul_left (fun y : ℝ => Real.sinc y ^ 4) π
  simp only at hc
  rw [integral_sinc_pi_pow_four] at hc
  have hpi : (0 : ℝ) < π := Real.pi_pos
  rw [abs_of_pos (by positivity), smul_eq_mul] at hc
  have hsinc4 : ∫ y : ℝ, Real.sinc y ^ 4 = 2 * π / 3 := by
    field_simp at hc ⊢
    linarith [hc]
  rw [← hsinc4]
  apply MeasureTheory.integral_congr_ae
  have hae : ∀ᵐ x : ℝ, x ≠ 0 := by
    rw [MeasureTheory.ae_iff]; simp
  filter_upwards [hae] with x hx
  rw [Real.sinc_of_ne_zero hx]

end Zeta23Scaffold

