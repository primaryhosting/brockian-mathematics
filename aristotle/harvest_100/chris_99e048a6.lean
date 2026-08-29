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
noncomputable def tent (x : ℝ) : ℂ := ((max 0 (1 - |x|) : ℝ) : ℂ)

lemma continuous_tent : Continuous tent := by
  unfold tent
  fun_prop

lemma tent_neg (x : ℝ) : tent (-x) = tent x := by
  simp [tent]

lemma tent_eq_zero_of_one_le (x : ℝ) (hx : 1 ≤ |x|) : tent x = 0 := by
  simp only [tent, Complex.ofReal_eq_zero]
  exact max_eq_left (by linarith)

lemma hasCompactSupport_tent : HasCompactSupport tent := by
  apply HasCompactSupport.intro (isCompact_Icc (a := (-1 : ℝ)) (b := 1))
  intro x hx
  apply tent_eq_zero_of_one_le
  simp only [Set.mem_Icc, not_and_or, not_le] at hx
  rcases hx with h | h
  · rw [abs_of_nonpos (by linarith)]; linarith
  · rw [abs_of_nonneg (by linarith)]; linarith

lemma integrable_tent : Integrable tent :=
  continuous_tent.integrable_of_hasCompactSupport hasCompactSupport_tent

/-- An integral over `ℝ` of a function supported in `[-1, 1]` is an interval integral. -/
lemma integral_eq_intervalIntegral_of_support {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℝ → E) (h : ∀ x : ℝ, 1 ≤ |x| → f x = 0) :
    ∫ x : ℝ, f x = ∫ x in (-1 : ℝ)..1, f x := by
  rw [intervalIntegral.integral_of_le (by norm_num),
    ← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (s := Set.Ioc (-1 : ℝ) 1)]
  intro x hx
  apply h
  simp only [Set.mem_Ioc, not_and_or, not_le, not_lt] at hx
  rcases hx with hx | hx
  · rw [abs_of_nonpos (by linarith)]; linarith
  · rw [abs_of_nonneg (by linarith)]; linarith

/-- `∫_ℝ (max 0 (1 - |x|))^n = 2/(n+1)` for `n ≥ 1`. -/
lemma integral_tent_pow (n : ℕ) (hn : n ≠ 0) :
    ∫ x : ℝ, (max 0 (1 - |x|)) ^ n = 2 / (n + 1) := by
  have key : ∫ x : ℝ, (max 0 (1 - |x|)) ^ n = ∫ x in (-1 : ℝ)..1, (max 0 (1 - |x|)) ^ n := by
    apply integral_eq_intervalIntegral_of_support
    intro x hx
    rw [max_eq_left (by linarith), zero_pow hn]
  rw [key, ← intervalIntegral.integral_add_adjacent_intervals (b := (0 : ℝ)) (a := -1) (c := 1)
      (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _)]
  have h1 : ∫ x in (-1 : ℝ)..0, (max 0 (1 - |x|)) ^ n = ∫ x in (-1 : ℝ)..0, (1 + x) ^ n := by
    apply intervalIntegral.integral_congr
    intro x hx
    simp only [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 0), Set.mem_Icc] at hx
    dsimp only
    rw [abs_of_nonpos hx.2, max_eq_right (by linarith)]
    ring_nf
  have h2 : ∫ x in (0 : ℝ)..1, (max 0 (1 - |x|)) ^ n = ∫ x in (0 : ℝ)..1, (1 - x) ^ n := by
    apply intervalIntegral.integral_congr
    intro x hx
    simp only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1), Set.mem_Icc] at hx
    dsimp only
    rw [abs_of_nonneg hx.1, max_eq_right (by linarith)]
  rw [h1, h2,
    show (fun x : ℝ => (1 + x) ^ n) = (fun x : ℝ => (fun y : ℝ => y ^ n) (x + 1)) by
      ext x; ring_nf,
    show (fun x : ℝ => (1 - x) ^ n) = (fun x : ℝ => (fun y : ℝ => y ^ n) (1 - x)) by
      ext x; ring_nf,
    intervalIntegral.integral_comp_add_right (fun y : ℝ => y ^ n) 1,
    intervalIntegral.integral_comp_sub_left (fun y : ℝ => y ^ n) 1]
  norm_num [integral_pow]
  ring

/-- The Fourier transform of the tent function, written as an interval integral. -/
lemma fourier_tent_eq_intervalIntegral (ξ : ℝ) :
    𝓕 tent ξ = ∫ v in (-1 : ℝ)..1, Complex.exp (-((2 * π * ξ * I) * v)) * tent v := by
  rw [Real.fourier_real_eq_integral_exp_smul, integral_eq_intervalIntegral_of_support]
  · apply intervalIntegral.integral_congr
    intro v _
    dsimp only
    rw [smul_eq_mul]
    congr 2
    push_cast
    ring
  · intro x hx
    rw [tent_eq_zero_of_one_le x hx, smul_zero]

/-- The basic antiderivative computation behind the Fourier transform of the tent function. -/
lemma tent_exp_integral (c : ℂ) (hc : c ≠ 0) :
    (∫ v in (-1 : ℝ)..0, Complex.exp (-(c * v)) * (1 + v))
      + (∫ v in (0 : ℝ)..1, Complex.exp (-(c * v)) * (1 - v))
      = (Complex.exp c + Complex.exp (-c) - 2) / c ^ 2 := by
  have hv : ∀ v : ℝ, HasDerivAt (fun v : ℝ => (v : ℂ)) 1 v := fun v => Complex.ofRealCLM.hasDerivAt
  have hexp : ∀ v : ℝ, HasDerivAt (fun v : ℝ => Complex.exp (-(c * v)))
      (Complex.exp (-(c * v)) * (-c)) v := by
    intro v
    have h1 : HasDerivAt (fun v : ℝ => -(c * (v : ℂ))) (-c) v := by
      simpa using (((hv v).const_mul c).neg)
    exact h1.cexp
  have hF : ∀ v : ℝ, HasDerivAt (fun v : ℝ => Complex.exp (-(c * v)) * (1 / c ^ 2 - (1 - v) / c))
      (Complex.exp (-(c * v)) * (1 - v)) v := by
    intro v
    have h4 : HasDerivAt (fun v : ℝ => (1 - (v : ℂ)) / c) (-(1 / c)) v := by
      simpa [div_eq_mul_inv] using ((((hv v).const_sub 1)).div_const c)
    have h3 : HasDerivAt (fun v : ℝ => (1 / c ^ 2 - (1 - (v : ℂ)) / c)) (-(-(1 / c))) v :=
      h4.const_sub (1 / c ^ 2)
    have h5 := (hexp v).mul h3
    convert h5 using 1
    field_simp
    ring
  have hG : ∀ v : ℝ,
      HasDerivAt (fun v : ℝ => Complex.exp (-(c * v)) * (-(1 / c ^ 2) - (1 + v) / c))
      (Complex.exp (-(c * v)) * (1 + v)) v := by
    intro v
    have h4 : HasDerivAt (fun v : ℝ => (1 + (v : ℂ)) / c) (1 / c) v := by
      simpa [div_eq_mul_inv] using ((((hv v).const_add 1)).div_const c)
    have h3 : HasDerivAt (fun v : ℝ => (-(1 / c ^ 2) - (1 + (v : ℂ)) / c)) (-(1 / c)) v :=
      h4.const_sub (-(1 / c ^ 2))
    have h5 := (hexp v).mul h3
    convert h5 using 1
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => hG v)
      (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => hF v)
      (by apply Continuous.intervalIntegrable; fun_prop)]
  push_cast
  simp only [mul_zero, neg_zero, Complex.exp_zero, mul_neg, mul_one]
  field_simp
  ring

/-- The Fourier transform of the tent function is `sinc (π ξ)²`. -/
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

lemma sinc_sq_le (t : ℝ) : Real.sinc t ^ 2 ≤ 2 / (1 + t ^ 2) := by
  have hpos : (0 : ℝ) < 1 + t ^ 2 := by positivity
  rcases eq_or_ne t 0 with rfl | ht
  · norm_num
  · have ht2 : (0 : ℝ) < t ^ 2 := by positivity
    rw [Real.sinc_of_ne_zero ht, div_pow, div_le_div_iff₀ ht2 hpos]
    have hs1 : Real.sin t ^ 2 ≤ 1 := by
      nlinarith [Real.neg_one_le_sin t, Real.sin_le_one t]
    have hs2 : Real.sin t ^ 2 ≤ t ^ 2 := by
      have := Real.abs_sin_le_abs (x := t)
      nlinarith [abs_nonneg (Real.sin t), abs_nonneg t, sq_abs (Real.sin t), sq_abs t]
    rcases le_total (t ^ 2) 1 with h | h
    · nlinarith
    · nlinarith

lemma integrable_fourier_tent : Integrable (𝓕 tent) := by
  have hrw : 𝓕 tent = fun ξ : ℝ => ((Real.sinc (π * ξ) ^ 2 : ℝ) : ℂ) := funext fourier_tent
  rw [hrw]
  apply Integrable.ofReal
  have hg : Integrable (fun ξ : ℝ => 2 * (1 + ξ ^ 2)⁻¹) := integrable_inv_one_add_sq.const_mul 2
  apply Integrable.mono' hg
  · exact ((Real.continuous_sinc.comp (by fun_prop)).pow 2).aestronglyMeasurable
  · filter_upwards with ξ
    show ‖Real.sinc (π * ξ) ^ 2‖ ≤ 2 * (1 + ξ ^ 2)⁻¹
    have h1 : Real.sinc (π * ξ) ^ 2 ≤ 2 / (1 + (π * ξ) ^ 2) := sinc_sq_le _
    have h2 : (0 : ℝ) ≤ Real.sinc (π * ξ) ^ 2 := sq_nonneg _
    have hpi : (1 : ℝ) ≤ π ^ 2 := by nlinarith [Real.pi_gt_three]
    have h3 : (1 : ℝ) + ξ ^ 2 ≤ 1 + (π * ξ) ^ 2 := by
      rw [mul_pow]; nlinarith [sq_nonneg ξ]
    have h4 : 2 / (1 + (π * ξ) ^ 2) ≤ 2 / (1 + ξ ^ 2) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) h3
    have h5 : 2 * (1 + ξ ^ 2)⁻¹ = 2 / (1 + ξ ^ 2) := by ring
    rw [Real.norm_of_nonneg h2, h5]
    linarith

/-- `∫ (tent)² = 2/3`. -/
lemma integral_tent_sq : ∫ x : ℝ, (max 0 (1 - |x|)) ^ 2 = 2 / 3 := by
  have h := integral_tent_pow 2 two_ne_zero
  norm_num at h
  exact h

/-- The key Parseval computation: `∫ sinc (π ξ)⁴ dξ = 2/3`. -/
lemma integral_sinc_pi_pow_four : ∫ ξ : ℝ, Real.sinc (π * ξ) ^ 4 = 2 / 3 := by
  have hflip : (innerₗ ℝ : ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ).flip = innerₗ ℝ := by
    ext
    simp
  have mult : ∫ ξ, (𝓕 tent ξ) * (𝓕 tent ξ) = ∫ x, (tent x) * (𝓕 (𝓕 tent) x) := by
    have := VectorFourier.integral_fourierIntegral_smul_eq_flip
      (L := (innerₗ ℝ : ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ)) (e := 𝐞) (μ := volume) (ν := volume)
      (f := tent) (g := 𝓕 tent) continuous_fourierChar (by fun_prop)
      integrable_tent integrable_fourier_tent
    rw [hflip] at this
    simpa [smul_eq_mul] using this
  have inv : ∀ x : ℝ, 𝓕 (𝓕 tent) x = tent x := by
    intro x
    have h := Real.fourierInv_eq_fourier_neg (𝓕 tent) (-x)
    rw [neg_neg] at h
    rw [← h, continuous_tent.fourierInv_fourier_eq integrable_tent integrable_fourier_tent,
      tent_neg]
  simp only [inv, fourier_tent] at mult
  have hl : ∫ ξ : ℝ, ((Real.sinc (π * ξ) ^ 2 : ℝ) : ℂ) * ((Real.sinc (π * ξ) ^ 2 : ℝ) : ℂ)
      = ((∫ ξ : ℝ, Real.sinc (π * ξ) ^ 4 : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    congr 1
    ext ξ
    push_cast
    ring
  have hr : ∫ x : ℝ, tent x * tent x = ((∫ x : ℝ, (max 0 (1 - |x|)) ^ 2 : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    congr 1
    ext x
    simp [tent]
    ring
  rw [hl, hr, integral_tent_sq] at mult
  exact_mod_cast mult

/-- **The integral of `(sin x / x)^4` over `ℝ` equals `2π/3`.** -/
theorem integral_sinc_fourth : ∫ x : ℝ, (Real.sin x / x) ^ 4 = 2 * Real.pi / 3 := by
  have h := integral_sinc_pi_pow_four
  have hae : ∀ᵐ ξ : ℝ, Real.sinc (π * ξ) ^ 4 = (Real.sin (π * ξ) / (π * ξ)) ^ 4 := by
    have h0 : ∀ᵐ ξ : ℝ, ξ ≠ 0 := by
      rw [MeasureTheory.ae_iff]; simp
    filter_upwards [h0] with ξ hξ
    rw [Real.sinc_of_ne_zero (by positivity)]
  rw [MeasureTheory.integral_congr_ae hae,
    MeasureTheory.Measure.integral_comp_mul_left (fun x : ℝ => (Real.sin x / x) ^ 4) π,
    abs_of_pos (by positivity : (0 : ℝ) < π⁻¹), smul_eq_mul] at h
  have hpi := Real.pi_pos
  simp only [div_pow] at h ⊢
  field_simp at h
  linarith

end Zeta23Scaffold

