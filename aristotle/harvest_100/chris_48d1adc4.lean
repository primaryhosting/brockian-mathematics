/-
# Integral Sinc Fourth
Category: C Integral
Target: Zeta23Scaffold.integral_sinc_fourth
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Integral Sinc Fourth
Category: C Integral
Target: Zeta23Scaffold.integral_sinc_fourth
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

We prove `∫ x : ℝ, (sin x / x) ^ 4 = 2 * π / 3`.

The argument is the classical Fourier-analytic one.  Let `tent` be the triangle function
`t ↦ max (1 - |t|) 0`.  Its Fourier transform is `ξ ↦ sinc (π ξ) ^ 2`.  The multiplication
(Parseval) formula `∫ 𝓕 f * g = ∫ f * 𝓕 g`, applied with `f = tent` and `g = 𝓕 tent`,
together with Fourier inversion (`𝓕 (𝓕 tent) = tent ∘ neg`), gives

`∫ sinc (π ξ) ^ 4 dξ = ∫ tent ^ 2 = 2 / 3`,

and a change of variables `x = π ξ` yields the result.
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

open MeasureTheory FourierTransform Real Complex

/-- The tent (triangle) function, supported on `[-1, 1]`. -/
noncomputable def tent (t : ℝ) : ℝ := max (1 - |t|) 0

/-- The tent function, viewed as a complex-valued function. -/
noncomputable def tentC (t : ℝ) : ℂ := (tent t : ℂ)

/-- The square of the sinc function at `π x`: the Fourier transform of `tent`. -/
noncomputable def sincSq (x : ℝ) : ℂ := ((Real.sinc (π * x)) ^ 2 : ℝ)

lemma tent_eq_zero_of_one_le {t : ℝ} (ht : 1 ≤ |t|) : tent t = 0 := by
  simp only [tent, max_eq_right_iff]
  linarith

lemma tent_neg (t : ℝ) : tent (-t) = tent t := by simp [tent]

lemma continuous_tent : Continuous tent := by
  unfold tent
  fun_prop

lemma continuous_tentC : Continuous tentC :=
  Complex.continuous_ofReal.comp continuous_tent

lemma tentC_eq_zero_of_notMem {t : ℝ} (ht : t ∉ Set.Icc (-1 : ℝ) 1) : tentC t = 0 := by
  simp only [Set.mem_Icc, not_and_or, not_le] at ht
  have : 1 ≤ |t| := by
    rcases ht with h | h
    · rw [abs_of_nonpos (by linarith)]; linarith
    · rw [abs_of_nonneg (by linarith)]; linarith
  simp [tentC, tent_eq_zero_of_one_le this]

lemma hasCompactSupport_tentC : HasCompactSupport tentC := by
  apply HasCompactSupport.intro (isCompact_Icc (a := (-1 : ℝ)) (b := 1))
  exact fun x hx => tentC_eq_zero_of_notMem hx

lemma integrable_tentC : Integrable tentC :=
  continuous_tentC.integrable_of_hasCompactSupport hasCompactSupport_tentC

/-- Multiplying a continuous function by the tent function and integrating over `ℝ` can be
computed as the sum of two interval integrals, on which the tent function is affine. -/
lemma integral_mul_tentC {g : ℝ → ℂ} (hg : Continuous g) :
    ∫ t : ℝ, g t * tentC t =
      (∫ t in (-1 : ℝ)..0, g t * (1 + 1 * (t : ℂ))) +
        ∫ t in (0 : ℝ)..1, g t * (1 + (-1) * (t : ℂ)) := by
  have h0 : ∀ t : ℝ, t ∉ Set.Icc (-1 : ℝ) 1 → g t * tentC t = 0 := by
    intro t ht
    simp [tentC_eq_zero_of_notMem ht]
  have hcont : Continuous fun t : ℝ => g t * tentC t := hg.mul continuous_tentC
  have hstep : ∫ t : ℝ, g t * tentC t = ∫ t in (-1 : ℝ)..1, g t * tentC t := by
    rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero h0,
      MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  have hsplit : ∫ t in (-1 : ℝ)..1, g t * tentC t =
      (∫ t in (-1 : ℝ)..0, g t * tentC t) + ∫ t in (0 : ℝ)..1, g t * tentC t :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)).symm
  have e1 : ∫ t in (-1 : ℝ)..0, g t * tentC t
      = ∫ t in (-1 : ℝ)..0, g t * (1 + 1 * (t : ℂ)) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 0)] at ht
    obtain ⟨h1, h2⟩ := ht
    have : tent t = 1 + t := by
      unfold tent; rw [abs_of_nonpos h2, max_eq_left (by linarith)]; ring
    simp only [tentC, this]
    push_cast
    ring
  have e2 : ∫ t in (0 : ℝ)..1, g t * tentC t
      = ∫ t in (0 : ℝ)..1, g t * (1 + (-1) * (t : ℂ)) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    obtain ⟨h1, h2⟩ := ht
    have : tent t = 1 - t := by
      unfold tent; rw [abs_of_nonneg h1, max_eq_left (by linarith)]
    simp only [tentC, this]
    push_cast
    ring
  rw [hstep, hsplit, e1, e2]

/-- The antiderivative computation `∫ exp (c t) (A + B t) dt`. -/
lemma integral_cexp_mul_linear (c : ℂ) (hc : c ≠ 0) (A B : ℂ) (u v : ℝ) :
    ∫ t in u..v, Complex.exp (c * t) * (A + B * t) =
      Complex.exp (c * v) * ((A - B / c) / c + (B / c) * v) -
        Complex.exp (c * u) * ((A - B / c) / c + (B / c) * u) := by
  have hcp : c * ((A - B / c) / c) + B / c = A := by field_simp; ring
  have hcq : c * (B / c) = B := by field_simp
  have hd : ∀ t : ℝ, HasDerivAt
      (fun s : ℝ => Complex.exp (c * s) * ((A - B / c) / c + (B / c) * s))
      (Complex.exp (c * t) * (A + B * t)) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := by
      simpa using Complex.ofRealCLM.hasDerivAt (x := t)
    have h2 : HasDerivAt (fun s : ℝ => Complex.exp (c * s)) (Complex.exp (c * t) * (c * 1)) t :=
      (h1.const_mul c).cexp
    have h3 : HasDerivAt (fun s : ℝ => (A - B / c) / c + (B / c) * (s : ℂ)) ((B / c) * 1) t :=
      (h1.const_mul (B / c)).const_add _
    refine (h2.mul h3).congr_deriv ?_
    calc Complex.exp (c * t) * (c * 1) * ((A - B / c) / c + (B / c) * t)
            + Complex.exp (c * t) * ((B / c) * 1)
        = Complex.exp (c * t) * ((c * ((A - B / c) / c) + B / c) + (c * (B / c)) * t) := by ring
      _ = Complex.exp (c * t) * (A + B * t) := by rw [hcp, hcq]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    (Continuous.intervalIntegrable (by fun_prop) _ _)

/-- The Fourier transform of the tent function at a nonzero point. -/
lemma fourier_tentC_of_ne {ξ : ℝ} (hξ : ξ ≠ 0) : 𝓕 tentC ξ = sincSq ξ := by
  set c : ℂ := -(2 * π * ξ) * I with hcdef
  have hc : c ≠ 0 := by
    rw [hcdef]
    simp [Complex.I_ne_zero, Real.pi_ne_zero, hξ]
  have hstep : 𝓕 tentC ξ = ∫ t : ℝ, Complex.exp (c * t) * tentC t := by
    rw [Real.fourier_eq']
    congr 1
    funext t
    congr 1
    · congr 1
      rw [hcdef]
      push_cast
      simp
      ring
  rw [hstep, integral_mul_tentC (g := fun t : ℝ => Complex.exp (c * t))
      (Complex.continuous_exp.comp (by fun_prop)),
    integral_cexp_mul_linear c hc, integral_cexp_mul_linear c hc]
  have hcollect :
      (Complex.exp (c * ((0 : ℝ) : ℂ)) * (((1 : ℂ) - 1 / c) / c + (1 / c) * ((0 : ℝ) : ℂ)) -
        Complex.exp (c * ((-1 : ℝ) : ℂ)) * (((1 : ℂ) - 1 / c) / c + (1 / c) * ((-1 : ℝ) : ℂ))) +
      (Complex.exp (c * ((1 : ℝ) : ℂ)) * (((1 : ℂ) - (-1) / c) / c + ((-1) / c) * ((1 : ℝ) : ℂ)) -
        Complex.exp (c * ((0 : ℝ) : ℂ)) * (((1 : ℂ) - (-1) / c) / c + ((-1) / c) * ((0 : ℝ) : ℂ)))
      = (Complex.exp c + Complex.exp (-c) - 2) / c ^ 2 := by
    push_cast
    simp only [mul_zero, mul_one, Complex.exp_zero]
    field_simp
    ring
  rw [hcollect, hcdef]
  -- final trigonometric identity
  have hpx : π * ξ ≠ 0 := mul_ne_zero Real.pi_ne_zero hξ
  have hcos : Complex.exp (-(2 * π * ξ) * I) + Complex.exp (-(-(2 * π * ξ) * I))
      = 2 * Complex.cos ((2 * π * ξ : ℝ) : ℂ) := by
    rw [Complex.two_cos]
    push_cast
    ring_nf
  rw [hcos, ← Complex.ofReal_cos]
  have hI : ((-(2 * π * ξ) * I)) ^ 2 = ((-(2 * π * ξ) ^ 2 : ℝ) : ℂ) := by
    push_cast
    rw [mul_pow, Complex.I_sq]
    ring
  rw [hI, sincSq, Real.sinc_of_ne_zero hpx, ← Complex.ofReal_ofNat 2, ← Complex.ofReal_mul,
    ← Complex.ofReal_sub, ← Complex.ofReal_div]
  norm_cast
  have h2 : Real.cos (2 * π * ξ) = 1 - 2 * Real.sin (π * ξ) ^ 2 := by
    have h : (2 : ℝ) * π * ξ = 2 * (π * ξ) := by ring
    rw [h, Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq (π * ξ)]
  rw [h2]
  field_simp
  ring

lemma continuous_sincSq : Continuous sincSq :=
  Complex.continuous_ofReal.comp
    ((Real.continuous_sinc.comp (continuous_const.mul continuous_id)).pow 2)

/-- The Fourier transform of the tent function is `ξ ↦ sinc (π ξ) ^ 2`. -/
lemma fourier_tentC : 𝓕 tentC = sincSq := by
  have hcont : Continuous (𝓕 tentC) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner
      integrable_tentC
  refine Continuous.ext_on (dense_compl_singleton (0 : ℝ)) hcont continuous_sincSq ?_
  intro ξ hξ
  exact fourier_tentC_of_ne (by simpa using hξ)

lemma norm_sincSq (x : ℝ) : ‖sincSq x‖ = (Real.sinc (π * x)) ^ 2 := by
  rw [sincSq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

lemma sinc_sq_le (x : ℝ) : (Real.sinc (π * x)) ^ 2 ≤ 2 * (1 + x ^ 2)⁻¹ := by
  have hpos : (0 : ℝ) < 1 + x ^ 2 := by positivity
  rw [show (2 : ℝ) * (1 + x ^ 2)⁻¹ = 2 / (1 + x ^ 2) by ring, le_div_iff₀ hpos]
  have h1 : (Real.sinc (π * x)) ^ 2 ≤ 1 := by
    have := Real.abs_sinc_le_one (π * x)
    nlinarith [abs_nonneg (Real.sinc (π * x)), sq_abs (Real.sinc (π * x))]
  have h2 : (Real.sinc (π * x)) ^ 2 * x ^ 2 ≤ 1 := by
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · have hpx : π * x ≠ 0 := mul_ne_zero Real.pi_ne_zero hx
      rw [Real.sinc_of_ne_zero hpx, div_pow, show (π * x) ^ 2 = π ^ 2 * x ^ 2 by ring]
      have hs : Real.sin (π * x) ^ 2 ≤ 1 := by
        nlinarith [Real.neg_one_le_sin (π * x), Real.sin_le_one (π * x)]
      have hx2 : (0 : ℝ) < x ^ 2 := by positivity
      have hpi : (1 : ℝ) ≤ π ^ 2 := by nlinarith [Real.pi_gt_three]
      rw [div_mul_eq_mul_div, div_le_one (by positivity)]
      nlinarith
  nlinarith

lemma integrable_sincSq : Integrable sincSq := by
  apply MeasureTheory.Integrable.mono' (g := fun x : ℝ => 2 * (1 + x ^ 2)⁻¹)
    (integrable_inv_one_add_sq.const_mul 2) continuous_sincSq.aestronglyMeasurable
  filter_upwards with x
  rw [norm_sincSq]
  exact sinc_sq_le x

/-- Fourier inversion: the Fourier transform of `sincSq` is the (even) tent function. -/
lemma fourier_sincSq (x : ℝ) : 𝓕 sincSq x = tentC (-x) := by
  have hinv : 𝓕⁻ (𝓕 tentC) = tentC :=
    Continuous.fourierInv_fourier_eq continuous_tentC integrable_tentC
      (by rw [fourier_tentC]; exact integrable_sincSq)
  have h := Real.fourierInv_eq_fourier_neg (𝓕 tentC) (-x)
  rw [hinv] at h
  rw [← fourier_tentC]
  simpa using h.symm

/-- The multiplication (Parseval) formula for integrable functions on `ℝ`. -/
lemma integral_fourier_mul {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) :
    ∫ ξ, 𝓕 f ξ * g ξ = ∫ x, f x * 𝓕 g x := by
  simpa using VectorFourier.integral_bilin_fourierIntegral_eq_flip (ContinuousLinearMap.mul ℂ ℂ)
    (L := innerₗ ℝ) Real.continuous_fourierChar continuous_inner hf hg

lemma integral_tent_sq : ∫ x : ℝ, tent x * tent x = 2 / 3 := by
  have h0 : ∀ x : ℝ, x ∉ Set.Icc (-1 : ℝ) 1 → tent x * tent x = 0 := by
    intro x hx
    have := tentC_eq_zero_of_notMem hx
    simp only [tentC, Complex.ofReal_eq_zero] at this
    simp [this]
  have hint : ∀ a b : ℝ, IntervalIntegrable (fun x => tent x * tent x) MeasureTheory.volume a b :=
    fun a b => (continuous_tent.mul continuous_tent).intervalIntegrable a b
  rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero h0,
    MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
    ← intervalIntegral.integral_add_adjacent_intervals (f := fun x => tent x * tent x)
      (a := (-1 : ℝ)) (b := 0) (c := 1) (hint _ _) (hint _ _)]
  have e1 : ∫ x in (-1 : ℝ)..0, tent x * tent x = ∫ x in (-1 : ℝ)..0, (1 + 2 * x + x ^ 2) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 0)] at hx
    obtain ⟨h1, h2⟩ := hx
    have : tent x = 1 + x := by
      unfold tent; rw [abs_of_nonpos h2, max_eq_left (by linarith)]; ring
    simp only [this]; ring
  have e2 : ∫ x in (0 : ℝ)..1, tent x * tent x = ∫ x in (0 : ℝ)..1, (1 - 2 * x + x ^ 2) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    obtain ⟨h1, h2⟩ := hx
    have : tent x = 1 - x := by
      unfold tent; rw [abs_of_nonneg h1, max_eq_left (by linarith)]
    simp only [this]; ring
  rw [e1, e2]
  have h1 : (∫ x in (-1 : ℝ)..0, (1 + 2 * x + x ^ 2))
      = (0 + 0 ^ 2 + 0 ^ 3 / 3) - ((-1) + (-1 : ℝ) ^ 2 + (-1) ^ 3 / 3) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun y : ℝ => y + y ^ 2 + y ^ 3 / 3)
    · intro x _
      have h : HasDerivAt (fun y : ℝ => y + y ^ 2 + y ^ 3 / 3) (1 + 2 * x + 3 * x ^ 2 / 3) x :=
        ((hasDerivAt_id x).add ((hasDerivAt_pow 2 x).congr_deriv (by ring))).add
          (((hasDerivAt_pow 3 x).div_const 3).congr_deriv (by ring))
      exact h.congr_deriv (by ring)
    · exact Continuous.intervalIntegrable (by fun_prop) _ _
  have h2 : (∫ x in (0 : ℝ)..1, (1 - 2 * x + x ^ 2))
      = (1 - 1 ^ 2 + (1 : ℝ) ^ 3 / 3) - (0 - 0 ^ 2 + 0 ^ 3 / 3) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun y : ℝ => y - y ^ 2 + y ^ 3 / 3)
    · intro x _
      have h : HasDerivAt (fun y : ℝ => y - y ^ 2 + y ^ 3 / 3) (1 - 2 * x + 3 * x ^ 2 / 3) x :=
        ((hasDerivAt_id x).sub ((hasDerivAt_pow 2 x).congr_deriv (by ring))).add
          (((hasDerivAt_pow 3 x).div_const 3).congr_deriv (by ring))
      exact h.congr_deriv (by ring)
    · exact Continuous.intervalIntegrable (by fun_prop) _ _
  rw [h1, h2]; norm_num

lemma integral_sincSq_sq : ∫ ξ : ℝ, sincSq ξ * sincSq ξ = ((2 / 3 : ℝ) : ℂ) := by
  have hInt : Integrable (𝓕 tentC) := by rw [fourier_tentC]; exact integrable_sincSq
  have h1 := integral_fourier_mul integrable_tentC hInt
  rw [fourier_tentC] at h1
  have h2 : ∀ x : ℝ, tentC x * 𝓕 sincSq x = ((tent x * tent x : ℝ) : ℂ) := by
    intro x
    rw [fourier_sincSq, tentC, tentC, tent_neg]
    push_cast
    ring
  rw [h1]
  simp only [h2]
  rw [integral_complex_ofReal, integral_tent_sq]

lemma integral_sinc_pi_pow_four : ∫ ξ : ℝ, (Real.sinc (π * ξ)) ^ 4 = 2 / 3 := by
  have h : ∀ ξ : ℝ, sincSq ξ * sincSq ξ = (((Real.sinc (π * ξ)) ^ 4 : ℝ) : ℂ) := by
    intro ξ
    simp only [sincSq]
    push_cast
    ring
  have := integral_sincSq_sq
  simp only [h] at this
  rw [integral_complex_ofReal] at this
  exact_mod_cast this

/-- `∫ (sin x / x) ^ 4 dx = 2 π / 3`. -/
theorem integral_sinc_fourth : ∫ x : ℝ, (Real.sin x / x) ^ 4 = 2 * Real.pi / 3 := by
  have hcomp := Measure.integral_comp_mul_left (fun y : ℝ => Real.sinc y ^ 4) π
  simp only [] at hcomp
  rw [integral_sinc_pi_pow_four, abs_of_pos (by positivity : (0:ℝ) < π⁻¹), smul_eq_mul] at hcomp
  have hsinc : ∫ y : ℝ, Real.sinc y ^ 4 = 2 * Real.pi / 3 := by
    field_simp at hcomp ⊢
    linarith [hcomp]
  rw [← hsinc]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [compl_mem_ae_iff.2 (measure_singleton (0 : ℝ))] with x hx
  rw [Real.sinc_of_ne_zero (by simpa using hx)]

end Zeta23Scaffold

