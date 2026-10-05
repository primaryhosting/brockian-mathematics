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

open MeasureTheory Real FourierTransform Complex

namespace Zeta23Scaffold

/-! ## The tent function -/

/-- The tent (triangle) function, supported on `[-1, 1]`. -/
noncomputable def tent (x : ℝ) : ℝ := max (1 - |x|) 0

/-- The tent function, viewed as a complex-valued function. -/
noncomputable def tentC (x : ℝ) : ℂ := (tent x : ℂ)

lemma continuous_tent : Continuous tent := by unfold tent; fun_prop

lemma continuous_tentC : Continuous tentC :=
  Complex.continuous_ofReal.comp continuous_tent

lemma tent_eq_zero {x : ℝ} (hx : 1 ≤ |x|) : tent x = 0 := by
  unfold tent; simp; linarith

lemma tent_neg (x : ℝ) : tent (-x) = tent x := by unfold tent; rw [abs_neg]

lemma tentC_neg (x : ℝ) : tentC (-x) = tentC x := by unfold tentC; rw [tent_neg]

lemma hasCompactSupport_tentC : HasCompactSupport tentC := by
  apply HasCompactSupport.intro (isCompact_Icc (a := (-1:ℝ)) (b := 1))
  intro x hx
  simp only [Set.mem_Icc, not_and_or, not_le] at hx
  have h : (1:ℝ) ≤ |x| := by
    rcases hx with h | h
    · rw [abs_of_nonpos (by linarith)]; linarith
    · rw [abs_of_nonneg (by linarith)]; linarith
  simp [tentC, tent_eq_zero h]

lemma integrable_tentC : Integrable tentC :=
  continuous_tentC.integrable_of_hasCompactSupport hasCompactSupport_tentC

/-! ## The Fourier transform of the tent function -/

lemma tent_int01 (a : ℝ) (ha : a ≠ 0) :
    (∫ x in (0:ℝ)..1, Complex.exp ((-(a:ℂ) * Complex.I) * x) * ((1:ℂ) - x))
      = -Complex.exp (-(a:ℂ) * Complex.I) / (a:ℂ)^2 - Complex.I / (a:ℂ) + 1 / (a:ℂ)^2 := by
  have haC : (a:ℂ) ≠ 0 := by exact_mod_cast ha
  have key : ∀ x : ℝ, HasDerivAt
      (fun y : ℝ => Complex.exp ((-(a:ℂ) * Complex.I) * y) *
        (Complex.I * (1 - (y:ℂ)) / (a:ℂ) - 1 / (a:ℂ)^2))
      (Complex.exp ((-(a:ℂ) * Complex.I) * x) * ((1:ℂ) - x)) x := by
    intro x
    have h1 : HasDerivAt (fun y : ℝ => ((-(a:ℂ) * Complex.I) * (y:ℂ)))
        (-(a:ℂ) * Complex.I) x := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).const_mul (-(a:ℂ) * Complex.I)
    have h2 := h1.cexp
    have h3 : HasDerivAt (fun y : ℝ => (Complex.I * (1 - (y:ℂ)) / (a:ℂ) - 1 / (a:ℂ)^2))
        (-Complex.I / (a:ℂ)) x := by
      have h0 : HasDerivAt (fun y : ℝ => (y:ℂ)) 1 x := by
        simpa using Complex.ofRealCLM.hasDerivAt (x := x)
      have h4 := (h0.const_sub (1:ℂ)).mul_const ((a:ℂ)⁻¹)
      simpa [div_eq_mul_inv, mul_comm, mul_assoc, mul_left_comm] using
        ((h4.const_mul Complex.I).sub_const (1 / (a:ℂ)^2))
    have h5 := h2.mul h3
    convert h5 using 1
    field_simp
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => key x)]
  · push_cast
    field_simp
    simp only [mul_zero, neg_zero, Complex.exp_zero]
    ring
  · exact Continuous.intervalIntegrable (by fun_prop) _ _

lemma tent_intm10 (a : ℝ) (ha : a ≠ 0) :
    (∫ x in (-1:ℝ)..0, Complex.exp ((-(a:ℂ) * Complex.I) * x) * ((1:ℂ) + x))
      = Complex.I / (a:ℂ) + 1 / (a:ℂ)^2 - Complex.exp ((a:ℂ) * Complex.I) / (a:ℂ)^2 := by
  have haC : (a:ℂ) ≠ 0 := by exact_mod_cast ha
  have key : ∀ x : ℝ, HasDerivAt
      (fun y : ℝ => Complex.exp ((-(a:ℂ) * Complex.I) * y) *
        (Complex.I * (1 + (y:ℂ)) / (a:ℂ) + 1 / (a:ℂ)^2))
      (Complex.exp ((-(a:ℂ) * Complex.I) * x) * ((1:ℂ) + x)) x := by
    intro x
    have h1 : HasDerivAt (fun y : ℝ => ((-(a:ℂ) * Complex.I) * (y:ℂ)))
        (-(a:ℂ) * Complex.I) x := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).const_mul (-(a:ℂ) * Complex.I)
    have h2 := h1.cexp
    have h3 : HasDerivAt (fun y : ℝ => (Complex.I * (1 + (y:ℂ)) / (a:ℂ) + 1 / (a:ℂ)^2))
        (Complex.I / (a:ℂ)) x := by
      have h0 : HasDerivAt (fun y : ℝ => (y:ℂ)) 1 x := by
        simpa using Complex.ofRealCLM.hasDerivAt (x := x)
      have h4 := (h0.const_add (1:ℂ)).mul_const ((a:ℂ)⁻¹)
      simpa [div_eq_mul_inv, mul_comm, mul_assoc, mul_left_comm] using
        ((h4.const_mul Complex.I).add_const (1 / (a:ℂ)^2))
    have h5 := h2.mul h3
    convert h5 using 1
    field_simp
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => key x)]
  · push_cast
    field_simp
    simp only [mul_zero, neg_zero, Complex.exp_zero]
    ring
  · exact Continuous.intervalIntegrable (by fun_prop) _ _

lemma fourier_tent_interval (ξ : ℝ) :
    𝓕 tentC ξ = ∫ v in (-1:ℝ)..1,
      Complex.exp ((-((2 * π * ξ : ℝ) : ℂ) * Complex.I) * v) * tentC v := by
  rw [Real.fourier_real_eq_integral_exp_smul, intervalIntegral.integral_of_le (by norm_num),
    MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero]
  · congr 1
    ext v
    congr 2
    push_cast
    ring
  · intro x hx
    simp only [Set.mem_Ioc, not_and_or, not_lt, not_le] at hx
    have h : (1:ℝ) ≤ |x| := by
      rcases hx with h | h
      · rw [abs_of_nonpos (by linarith)]; linarith
      · rw [abs_of_nonneg (by linarith)]; linarith
    simp [tentC, tent_eq_zero h]

lemma tent_split (a : ℝ) :
    (∫ v in (-1:ℝ)..1, Complex.exp ((-(a:ℂ) * Complex.I) * v) * tentC v)
      = (∫ x in (-1:ℝ)..0, Complex.exp ((-(a:ℂ) * Complex.I) * x) * ((1:ℂ) + x))
        + (∫ x in (0:ℝ)..1, Complex.exp ((-(a:ℂ) * Complex.I) * x) * ((1:ℂ) - x)) := by
  have hcont : Continuous fun v : ℝ => Complex.exp ((-(a:ℂ) * Complex.I) * v) * tentC v :=
    (by fun_prop : Continuous fun v : ℝ =>
      Complex.exp ((-(a:ℂ) * Complex.I) * v)).mul continuous_tentC
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (-1:ℝ)) (b := 0) (c := 1)
    (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)]
  congr 1
  · apply intervalIntegral.integral_congr
    intro x hx
    simp only [Set.uIcc_of_le (by norm_num : (-1:ℝ) ≤ 0), Set.mem_Icc] at hx
    have h : tent x = 1 + x := by
      unfold tent
      rw [abs_of_nonpos hx.2]
      simp
      linarith [hx.1]
    simp [tentC, h]
  · apply intervalIntegral.integral_congr
    intro x hx
    simp only [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1), Set.mem_Icc] at hx
    have h : tent x = 1 - x := by
      unfold tent
      rw [abs_of_nonneg hx.1]
      simp
      linarith [hx.2]
    simp [tentC, h]

/-- The Fourier transform of the tent function is `sinc (π ξ) ^ 2`. -/
lemma fourier_tentC (ξ : ℝ) : 𝓕 tentC ξ = ((Real.sinc (π * ξ) ^ 2 : ℝ) : ℂ) := by
  rw [fourier_tent_interval, tent_split]
  rcases eq_or_ne ξ 0 with rfl | hξ
  · norm_num
    rw [intervalIntegral.integral_congr
        (g := fun x : ℝ => (1:ℂ) + x) (by intro x _; simp),
      intervalIntegral.integral_congr
        (g := fun x : ℝ => (1:ℂ) - x) (by intro x _; simp)]
    rw [intervalIntegral.integral_add (by fun_prop) (by fun_prop),
      intervalIntegral.integral_sub (by fun_prop) (by fun_prop)]
    simp [intervalIntegral.integral_comp_ofReal, integral_id]
    norm_num
  · have ha : (2 * π * ξ : ℝ) ≠ 0 := by
      have := Real.pi_ne_zero
      simp [mul_ne_zero, hξ, this]
    rw [tent_int01 _ ha, tent_intm10 _ ha]
    have haC : ((2 * π * ξ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ha
    have hexp : Complex.exp (((2 * π * ξ : ℝ) : ℂ) * Complex.I)
        + Complex.exp (-(((2 * π * ξ : ℝ) : ℂ)) * Complex.I)
        = 2 * ((Real.cos (2 * π * ξ) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cos, Complex.cos]
      ring_nf
    have hpiξ : π * ξ ≠ 0 := mul_ne_zero Real.pi_ne_zero hξ
    have hcos : 2 - 2 * Real.cos (2 * π * ξ) = 4 * Real.sin (π * ξ) ^ 2 := by
      have : (2 : ℝ) * π * ξ = 2 * (π * ξ) := by ring
      rw [this, Real.cos_two_mul']
      nlinarith [Real.sin_sq_add_cos_sq (π * ξ)]
    have hval : Real.sinc (π * ξ) ^ 2 = Real.sin (π * ξ) ^ 2 / (π * ξ) ^ 2 := by
      rw [Real.sinc_of_ne_zero hpiξ, div_pow]
    rw [hval]
    have hexpand : ((Real.sin (π * ξ) ^ 2 / (π * ξ) ^ 2 : ℝ) : ℂ)
        = ((Real.sin (π * ξ) ^ 2 : ℝ) : ℂ) / ((π * ξ : ℝ) : ℂ) ^ 2 := by
      push_cast; ring
    rw [hexpand]
    have h2 : ((2 * π * ξ : ℝ) : ℂ) = 2 * ((π * ξ : ℝ) : ℂ) := by push_cast; ring
    have hpiξC : ((π * ξ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpiξ
    have hsin : ((Real.sin (π * ξ) ^ 2 : ℝ) : ℂ)
        = (2 - 2 * ((Real.cos (2 * π * ξ) : ℝ) : ℂ)) / 4 := by
      have := congrArg (fun t : ℝ => (t : ℂ)) hcos
      push_cast at this ⊢
      linear_combination this / 4
    rw [hsin, h2]
    rw [div_add_div_same, div_sub_div_eq_sub_div, div_add_div_same, div_sub_div_eq_sub_div,
      div_add_div_same]
    rw [div_eq_div_iff (by positivity) (by positivity)]
    have := hexp
    rw [h2] at this
    field_simp
    linear_combination (4 * ((π:ℂ) * (ξ:ℂ))^2) * this

/-! ## Integrability of `sinc (π ξ) ^ 2` -/

lemma sinc_sq_le (u : ℝ) : Real.sinc u ^ 2 ≤ 2 / (1 + u^2) := by
  rcases le_or_gt |u| 1 with h | h
  · have h1 : Real.sinc u ^ 2 ≤ 1 := by
      nlinarith [Real.abs_sinc_le_one u, abs_nonneg (Real.sinc u), sq_abs (Real.sinc u)]
    have h2 : 1 + u^2 ≤ 2 := by nlinarith [sq_abs u, abs_nonneg u]
    have h3 : (0:ℝ) < 1 + u^2 := by positivity
    rw [le_div_iff₀ h3]; nlinarith
  · have hu : u ≠ 0 := by rintro rfl; simp at h; linarith
    have hu2 : 1 < u^2 := by nlinarith [sq_abs u, abs_nonneg u]
    rw [Real.sinc_of_ne_zero hu, div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [Real.sin_sq_le_one u]

lemma integrable_sincSqC :
    Integrable (fun ξ : ℝ => ((Real.sinc (π * ξ) ^ 2 : ℝ) : ℂ)) := by
  have hbase : Integrable (fun ξ : ℝ => 2 * (1 + (π * ξ)^2)⁻¹) := by
    refine Integrable.const_mul ?_ 2
    exact integrable_inv_one_add_sq.comp_mul_left' Real.pi_ne_zero
  refine hbase.mono' ?_ ?_
  · apply Continuous.aestronglyMeasurable
    exact Complex.continuous_ofReal.comp (by fun_prop)
  · filter_upwards with ξ
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have := sinc_sq_le (π * ξ)
    rwa [div_eq_mul_inv, mul_comm] at this
    
lemma integrable_fourier_tentC : Integrable (𝓕 tentC) := by
  have : 𝓕 tentC = fun ξ : ℝ => ((Real.sinc (π * ξ) ^ 2 : ℝ) : ℂ) := funext fourier_tentC
  rw [this]
  exact integrable_sincSqC

/-! ## Plancherel step -/

lemma multiplication_formula (f g : ℝ → ℂ) (hf : Integrable f) (hg : Integrable g) :
    ∫ ξ : ℝ, (𝓕 f ξ) * (g ξ) = ∫ x : ℝ, (f x) * (𝓕 g x) := by
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip (V := ℝ) (W := ℝ)
    (L := (innerₗ ℝ)) (μ := volume) (ν := volume) (e := 𝐞) (f := f) (g := g)
    Real.continuous_fourierChar (by fun_prop) hf hg
  simpa [smul_eq_mul, Real.fourier_eq] using h

lemma plancherel_tent :
    ∫ ξ : ℝ, (𝓕 tentC ξ) * (𝓕 tentC ξ) = ∫ x : ℝ, (tentC x) * (tentC x) := by
  rw [multiplication_formula tentC (𝓕 tentC) integrable_tentC integrable_fourier_tentC]
  congr 1
  ext x
  congr 1
  have hinv : 𝓕⁻ (𝓕 tentC) (-x) = tentC (-x) :=
    integrable_tentC.fourierInv_fourier_eq integrable_fourier_tentC
      continuous_tentC.continuousAt
  rw [Real.fourierInv_eq_fourier_neg] at hinv
  simpa [tentC_neg] using hinv

/-! ## The `L²` norm of the tent function -/

lemma integral_tent_sq : ∫ x : ℝ, (tent x)^2 = 2/3 := by
  have hsupp : ∀ x ∉ Set.Ioc (-1:ℝ) 1, (tent x)^2 = 0 := by
    intro x hx
    simp only [Set.mem_Ioc, not_and_or, not_lt, not_le] at hx
    have h : (1:ℝ) ≤ |x| := by
      rcases hx with h | h
      · rw [abs_of_nonpos (by linarith)]; linarith
      · rw [abs_of_nonneg (by linarith)]; linarith
    simp [tent_eq_zero h]
  rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hsupp,
    ← intervalIntegral.integral_of_le (by norm_num : (-1:ℝ) ≤ 1)]
  have hcont : Continuous fun x : ℝ => (tent x)^2 := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (a := (-1:ℝ)) (b := 0) (c := 1)
    (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)]
  have e1 : (∫ x in (-1:ℝ)..0, (tent x)^2) = ∫ x in (-1:ℝ)..0, (1 + x)^2 := by
    apply intervalIntegral.integral_congr
    intro x hx
    simp only [Set.uIcc_of_le (by norm_num : (-1:ℝ) ≤ 0), Set.mem_Icc] at hx
    have h : tent x = 1 + x := by
      unfold tent; rw [abs_of_nonpos hx.2]; simp; linarith [hx.1]
    simp [h]
  have e2 : (∫ x in (0:ℝ)..1, (tent x)^2) = ∫ x in (0:ℝ)..1, (1 - x)^2 := by
    apply intervalIntegral.integral_congr
    intro x hx
    simp only [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1), Set.mem_Icc] at hx
    have h : tent x = 1 - x := by
      unfold tent; rw [abs_of_nonneg hx.1]; simp; linarith [hx.2]
    simp [h]
  rw [e1, e2]
  have d1 : ∀ x : ℝ, HasDerivAt (fun y : ℝ => (1 + y)^3 / 3) ((1 + x)^2) x := by
    intro x
    have := ((hasDerivAt_id x).const_add (1:ℝ)).pow 3
    simpa using this.div_const 3
  have d2 : ∀ x : ℝ, HasDerivAt (fun y : ℝ => -(1 - y)^3 / 3) ((1 - x)^2) x := by
    intro x
    have := ((hasDerivAt_id x).const_sub (1:ℝ)).pow 3
    have h2 := (this.neg).div_const 3
    convert h2 using 1
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => d1 x)
      (Continuous.intervalIntegrable (by fun_prop) _ _),
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => d2 x)
      (Continuous.intervalIntegrable (by fun_prop) _ _)]
  norm_num

/-! ## Putting it together -/

lemma integral_sinc_pi_fourth : ∫ ξ : ℝ, (Real.sinc (π * ξ))^4 = 2/3 := by
  have hL : ∫ ξ : ℝ, (𝓕 tentC ξ) * (𝓕 tentC ξ)
      = ((∫ ξ : ℝ, (Real.sinc (π * ξ))^4 : ℝ) : ℂ) := by
    rw [← MeasureTheory.integral_ofReal]
    congr 1
    ext ξ
    rw [fourier_tentC]
    push_cast
    ring
  have hR : ∫ x : ℝ, (tentC x) * (tentC x) = ((∫ x : ℝ, (tent x)^2 : ℝ) : ℂ) := by
    rw [← MeasureTheory.integral_ofReal]
    congr 1
    ext x
    simp [tentC]
    ring
  rw [hL, hR, integral_tent_sq] at plancherel_tent
  exact_mod_cast plancherel_tent

lemma integral_sinc_fourth' : ∫ x : ℝ, (Real.sinc x)^4 = 2 * π / 3 := by
  have h := Measure.integral_comp_mul_left (fun x : ℝ => (Real.sinc x)^4) π
  rw [integral_sinc_pi_fourth] at h
  rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ π⁻¹), smul_eq_mul] at h
  have hπ : (π:ℝ) ≠ 0 := Real.pi_ne_zero
  field_simp at h
  linarith [h]

theorem integral_sinc_fourth : ∫ x : ℝ, (Real.sin x / x)^4 = 2 * π / 3 := by
  rw [← integral_sinc_fourth']
  apply MeasureTheory.integral_congr_ae
  have h : ({(0:ℝ)}ᶜ : Set ℝ) ∈ (ae volume) := by
    rw [mem_ae_iff]
    simp
  filter_upwards [h] with x hx
  rw [Real.sinc_of_ne_zero hx]

end Zeta23Scaffold

