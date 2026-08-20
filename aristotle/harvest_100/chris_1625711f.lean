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

The header above is repeated as a plain comment on the first line of this file, since Lean 4
requires `import` commands to precede any module docstring.

## Method

With `T u = max 0 (1 - |u|)` the tent function, an explicit computation gives
`𝓕 T ξ = sinc (π ξ) ^ 2`.  The convolution theorem then yields `𝓕 (T ⋆ T) ξ = sinc (π ξ) ^ 4`,
and Fourier inversion at `0` gives
`∫ sinc (π ξ) ^ 4 dξ = (T ⋆ T) 0 = ∫ T ² = 2/3`.
Rescaling by `π` produces `∫ (sin x / x) ^ 4 dx = 2π/3`.
-/

open MeasureTheory Convolution FourierTransform
open scoped Real

namespace Zeta23Scaffold

/-- The tent (triangle) function `u ↦ max 0 (1 - |u|)`. -/
noncomputable def tent (u : ℝ) : ℝ := max 0 (1 - |u|)

/-- The tent function, viewed as a complex-valued function. -/
noncomputable def tentC (u : ℝ) : ℂ := (tent u : ℂ)

@[fun_prop]
lemma tent_continuous : Continuous tent := by
  unfold tent; fun_prop

lemma tent_eq_zero {u : ℝ} (h : 1 ≤ |u|) : tent u = 0 := by
  simp only [tent, max_eq_left_iff, sub_nonpos]
  linarith

lemma tent_nonneg (u : ℝ) : 0 ≤ tent u := le_max_left _ _

lemma tent_neg (u : ℝ) : tent (-u) = tent u := by simp [tent]

lemma tentC_continuous : Continuous tentC :=
  Complex.continuous_ofReal.comp tent_continuous

lemma tentC_hasCompactSupport : HasCompactSupport tentC := by
  apply HasCompactSupport.intro (isCompact_Icc (a := (-1 : ℝ)) (b := 1))
  intro x hx
  simp only [Set.mem_Icc, not_and_or, not_le] at hx
  have : 1 ≤ |x| := by
    rcases hx with h | h
    · rw [abs_of_nonpos (by linarith)]; linarith
    · rw [abs_of_nonneg (by linarith)]; linarith
  simp [tentC, tent_eq_zero this]

lemma tentC_integrable : Integrable tentC :=
  tentC_continuous.integrable_of_hasCompactSupport tentC_hasCompactSupport

/-- Splitting the integral of `exp (c v) * tent v` into the two linear pieces. -/
lemma integral_exp_mul_tentC_split (c : ℂ) :
    ∫ v : ℝ, Complex.exp (c * v) * tentC v
      = (∫ v in (-1:ℝ)..0, Complex.exp (c * v) * (1 + (v : ℂ)))
        + ∫ v in (0:ℝ)..1, Complex.exp (c * v) * (1 - (v : ℂ)) := by
  have hcont : Continuous (fun v : ℝ => Complex.exp (c * v) * tentC v) := by
    apply Continuous.mul _ tentC_continuous
    exact (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))
  have hsupp : ∀ x ∈ (Set.Icc (-1:ℝ) 1)ᶜ, Complex.exp (c * x) * tentC x = 0 := by
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le] at hx
    have : 1 ≤ |x| := by
      rcases hx with h | h
      · rw [abs_of_nonpos (by linarith)]; linarith
      · rw [abs_of_nonneg (by linarith)]; linarith
    simp [tentC, tent_eq_zero this]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hsupp,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (-1:ℝ) ≤ 1),
    ← intervalIntegral.integral_add_adjacent_intervals (a := (-1:ℝ)) (b := 0) (c := 1)
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)]
  congr 1
  · apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by norm_num)] at hx
    have hax : |x| = -x := abs_of_nonpos hx.2
    simp only [tentC, tent, hax]
    rw [max_eq_right (by linarith [hx.1])]
    push_cast; ring
  · apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by norm_num)] at hx
    have hax : |x| = x := abs_of_nonneg hx.1
    simp only [tentC, tent, hax]
    rw [max_eq_right (by linarith [hx.2])]
    push_cast; ring

lemma integral_exp_mul_one_sub (c : ℂ) (hc : c ≠ 0) :
    (∫ u in (0:ℝ)..1, Complex.exp (c * u) * (1 - (u : ℂ)))
      = Complex.exp c / c ^ 2 - (1 / c + 1 / c ^ 2) := by
  have key : ∀ u : ℝ, HasDerivAt
      (fun t : ℝ => Complex.exp (c * t) * (-(1 / c) * (t : ℂ) + (1 + 1 / c) / c))
      (Complex.exp (c * u) * (1 - (u : ℂ))) u := by
    intro u
    have h1 : HasDerivAt (fun t : ℝ => c * (t : ℂ)) c u := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := u)).const_mul c
    have h3 : HasDerivAt (fun t : ℝ => -(1 / c) * (t : ℂ) + (1 + 1 / c) / c) (-(1 / c)) u := by
      simpa using
        ((Complex.ofRealCLM.hasDerivAt (x := u)).const_mul (-(1 / c))).add_const ((1 + 1 / c) / c)
    have := h1.cexp.mul h3
    convert this using 1
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => key x)
    (by apply Continuous.intervalIntegrable; fun_prop)]
  push_cast
  field_simp
  simp only [mul_zero, Complex.exp_zero]
  ring

lemma integral_exp_mul_one_add (c : ℂ) (hc : c ≠ 0) :
    (∫ u in (-1:ℝ)..0, Complex.exp (c * u) * (1 + (u : ℂ)))
      = 1 / c - 1 / c ^ 2 + Complex.exp (-c) / c ^ 2 := by
  have key : ∀ u : ℝ, HasDerivAt
      (fun t : ℝ => Complex.exp (c * t) * ((1 / c) * (t : ℂ) + (1 - 1 / c) / c))
      (Complex.exp (c * u) * (1 + (u : ℂ))) u := by
    intro u
    have h1 : HasDerivAt (fun t : ℝ => c * (t : ℂ)) c u := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := u)).const_mul c
    have h3 : HasDerivAt (fun t : ℝ => (1 / c) * (t : ℂ) + (1 - 1 / c) / c) (1 / c) u := by
      simpa using
        ((Complex.ofRealCLM.hasDerivAt (x := u)).const_mul (1 / c)).add_const ((1 - 1 / c) / c)
    have := h1.cexp.mul h3
    convert this using 1
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => key x)
    (by apply Continuous.intervalIntegrable; fun_prop)]
  push_cast
  field_simp
  simp only [mul_zero, Complex.exp_zero]
  ring

lemma integral_exp_mul_tentC (c : ℂ) (hc : c ≠ 0) :
    ∫ v : ℝ, Complex.exp (c * v) * tentC v = (Complex.exp c + Complex.exp (-c) - 2) / c ^ 2 := by
  rw [integral_exp_mul_tentC_split c, integral_exp_mul_one_add c hc,
    integral_exp_mul_one_sub c hc]
  field_simp
  ring

/-- The tent function has integral `1`. -/
lemma integral_tentC : ∫ v : ℝ, tentC v = 1 := by
  have h := integral_exp_mul_tentC_split 0
  simp only [zero_mul, Complex.exp_zero, one_mul] at h
  rw [h]
  have d1 : ∀ u : ℝ, HasDerivAt (fun t : ℝ => (t : ℂ) + (t : ℂ) ^ 2 / 2) (1 + (u : ℂ)) u := by
    intro u
    have hd : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 u := Complex.ofRealCLM.hasDerivAt
    have := hd.add ((hd.pow 2).div_const 2)
    convert this using 1
    simp
  have d2 : ∀ u : ℝ, HasDerivAt (fun t : ℝ => (t : ℂ) - (t : ℂ) ^ 2 / 2) (1 - (u : ℂ)) u := by
    intro u
    have hd : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 u := Complex.ofRealCLM.hasDerivAt
    have := hd.sub ((hd.pow 2).div_const 2)
    convert this using 1
    simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => d1 x)
      (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => d2 x)
      (by apply Continuous.intervalIntegrable; fun_prop)]
  push_cast
  ring

/-- Fourier transform of the tent function: `𝓕 tent ξ = sinc (π ξ) ^ 2`. -/
lemma fourier_tentC (ξ : ℝ) : 𝓕 tentC ξ = ((Real.sinc (π * ξ) ^ 2 : ℝ) : ℂ) := by
  have hF : 𝓕 tentC ξ = ∫ v : ℝ, Complex.exp ((-(2 * π * ξ) * Complex.I) * v) * tentC v := by
    rw [Real.fourier_eq]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only [RCLike.inner_apply, conj_trivial, Circle.smul_def, Real.fourierChar_apply,
      smul_eq_mul]
    push_cast
    ring_nf
  rcases eq_or_ne ξ 0 with rfl | hξ
  · rw [hF]
    simpa using integral_tentC
  · set c : ℂ := -(2 * (π:ℂ) * (ξ:ℂ)) * Complex.I with hcdef
    have hy : (π * ξ) ≠ 0 := mul_ne_zero Real.pi_ne_zero hξ
    have hyC : ((π:ℂ) * (ξ:ℂ)) ≠ 0 := by simpa using Complex.ofReal_ne_zero.mpr hy
    have hc : c ≠ 0 := by
      simp only [hcdef]
      exact mul_ne_zero (by simpa using hyC) Complex.I_ne_zero
    have hsum : Complex.exp c + Complex.exp (-c) = ((2 * Real.cos (2 * π * ξ) : ℝ) : ℂ) := by
      have h1 : (-(2 * (π:ℂ) * (ξ:ℂ))) = ((-(2 * π * ξ) : ℝ) : ℂ) := by push_cast; ring
      have h2 : -(((-(2 * π * ξ) : ℝ) : ℂ) * Complex.I) = (((2 * π * ξ) : ℝ) : ℂ) * Complex.I := by
        push_cast; ring
      rw [hcdef, h1, Complex.exp_mul_I, h2, Complex.exp_mul_I, ← Complex.ofReal_cos,
        ← Complex.ofReal_cos, ← Complex.ofReal_sin, ← Complex.ofReal_sin]
      push_cast [Real.cos_neg, Real.sin_neg]
      ring
    rw [hF, integral_exp_mul_tentC c hc, hsum, Real.sinc_of_ne_zero hy, hcdef]
    have hcos : Real.cos (2 * π * ξ) = 1 - 2 * Real.sin (π * ξ) ^ 2 := by
      have h : (2:ℝ) * π * ξ = 2 * (π * ξ) := by ring
      rw [h, Real.cos_two_mul]
      nlinarith [Real.sin_sq_add_cos_sq (π * ξ)]
    rw [hcos]
    have hI : (-(2 * (π:ℂ) * (ξ:ℂ)) * Complex.I) ^ 2 = -(4 * ((π:ℂ) * (ξ:ℂ)) ^ 2) := by
      have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
      ring_nf
      rw [hI2]
      ring
    rw [hI]
    push_cast
    field_simp
    ring

/-- The self-convolution of the tent function. -/
noncomputable def gg : ℝ → ℂ := tentC ⋆[ContinuousLinearMap.mul ℂ ℂ] tentC

lemma gg_continuous : Continuous gg :=
  tentC_hasCompactSupport.continuous_convolution_right _
    tentC_integrable.locallyIntegrable tentC_continuous

lemma gg_hasCompactSupport : HasCompactSupport gg :=
  tentC_hasCompactSupport.convolution _ tentC_hasCompactSupport

lemma gg_integrable : Integrable gg :=
  gg_continuous.integrable_of_hasCompactSupport gg_hasCompactSupport

lemma fourier_gg (ξ : ℝ) : 𝓕 gg ξ = ((Real.sinc (π * ξ) ^ 4 : ℝ) : ℂ) := by
  rw [gg, Real.fourier_mul_convolution_eq tentC_integrable tentC_integrable
    tentC_continuous tentC_continuous, fourier_tentC]
  push_cast
  ring

lemma tent_sq_eq_zero_of_mem_compl {x : ℝ} (hx : x ∈ (Set.Icc (-1 : ℝ) 1)ᶜ) :
    tent x ^ 2 = 0 := by
  simp only [Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le] at hx
  have : 1 ≤ |x| := by
    rcases hx with h | h
    · rw [abs_of_nonpos (by linarith)]; linarith
    · rw [abs_of_nonneg (by linarith)]; linarith
  simp [tent_eq_zero this]

/-- The `L²` norm of the tent function: `∫ tent² = 2/3`. -/
lemma integral_tent_sq : ∫ t : ℝ, tent t ^ 2 = 2 / 3 := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => tent_sq_eq_zero_of_mem_compl hx),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (-1:ℝ) ≤ 1),
    ← intervalIntegral.integral_add_adjacent_intervals (a := (-1:ℝ)) (b := 0) (c := 1)
      (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop)]
  have h1 : ∫ x in (-1:ℝ)..0, tent x ^ 2 = ∫ x in (-1:ℝ)..0, (1 + x) ^ 2 := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by norm_num)] at hx
    have hax : |x| = -x := abs_of_nonpos hx.2
    simp only [tent, hax]
    rw [max_eq_right (by linarith [hx.1])]
    ring
  have h2 : ∫ x in (0:ℝ)..1, tent x ^ 2 = ∫ x in (0:ℝ)..1, (1 - x) ^ 2 := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by norm_num)] at hx
    have hax : |x| = x := abs_of_nonneg hx.1
    simp only [tent, hax]
    rw [max_eq_right (by linarith [hx.2])]
  have e1 : (∫ x in (-1:ℝ)..0, (1 + x) ^ 2) = 1 / 3 := by
    have hd : ∀ x : ℝ, HasDerivAt (fun t : ℝ => (1 + t) ^ 3 / 3) ((1 + x) ^ 2) x := by
      intro x
      have h : HasDerivAt (fun t : ℝ => 1 + t) 1 x := by
        simpa using (hasDerivAt_id x).const_add 1
      have := (h.pow 3).div_const 3
      convert this using 1
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
      (by apply Continuous.intervalIntegrable; fun_prop)]
    norm_num
  have e2 : (∫ x in (0:ℝ)..1, (1 - x) ^ 2) = 1 / 3 := by
    have hd : ∀ x : ℝ, HasDerivAt (fun t : ℝ => -(1 - t) ^ 3 / 3) ((1 - x) ^ 2) x := by
      intro x
      have h : HasDerivAt (fun t : ℝ => 1 - t) (-1) x := by
        simpa using (hasDerivAt_id x).const_sub 1
      have := ((h.pow 3).neg.div_const 3)
      convert this using 1
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
      (by apply Continuous.intervalIntegrable; fun_prop)]
    norm_num
  rw [h1, h2, e1, e2]
  norm_num

lemma gg_zero : gg 0 = ((2 : ℂ) / 3) := by
  rw [gg, convolution_def]
  have : ∀ t : ℝ, (ContinuousLinearMap.mul ℂ ℂ) (tentC t) (tentC (0 - t))
      = ((tent t ^ 2 : ℝ) : ℂ) := by
    intro t
    simp only [ContinuousLinearMap.mul_apply', zero_sub, tentC, tent_neg]
    push_cast
    ring
  simp only [this]
  rw [integral_complex_ofReal, integral_tent_sq]
  norm_num

/-- Pointwise bound `|sinc t| ^ 4 ≤ 2 / (1 + t²)`. -/
lemma abs_sinc_pow_four_le (t : ℝ) : |Real.sinc t ^ 4| ≤ 2 * (1 + t ^ 2)⁻¹ := by
  have hpos : (0:ℝ) < 1 + t ^ 2 := by positivity
  rw [abs_pow]
  rcases le_or_gt |t| 1 with h | h
  · have h1 : |Real.sinc t| ^ 4 ≤ 1 := by
      calc |Real.sinc t| ^ 4 ≤ 1 ^ 4 :=
            pow_le_pow_left₀ (abs_nonneg _) (Real.abs_sinc_le_one t) 4
        _ = 1 := one_pow 4
    have h2 : (1:ℝ) ≤ 2 * (1 + t ^ 2)⁻¹ := by
      rw [le_mul_inv_iff₀ hpos]
      nlinarith [sq_abs t, abs_nonneg t]
    linarith
  · have ht : t ≠ 0 := by
      intro h0; rw [h0] at h; simp at h; linarith
    have hta : (0:ℝ) < |t| := abs_pos.mpr ht
    have hs : |Real.sinc t| ≤ |t|⁻¹ := by
      rw [Real.sinc_of_ne_zero ht, abs_div, div_le_iff₀ hta, inv_mul_cancel₀ hta.ne']
      exact Real.abs_sin_le_one t
    have h1 : |Real.sinc t| ^ 4 ≤ (|t|⁻¹) ^ 4 := pow_le_pow_left₀ (abs_nonneg _) hs 4
    have h2 : (|t|⁻¹) ^ 4 ≤ 2 * (1 + t ^ 2)⁻¹ := by
      rw [show ((|t|⁻¹ : ℝ)) ^ 4 = 1 / |t| ^ 4 by rw [inv_pow]; ring,
        show (2:ℝ) * (1 + t ^ 2)⁻¹ = 2 / (1 + t ^ 2) by ring,
        div_le_div_iff₀ (by positivity) hpos, ← sq_abs t]
      have ha2 : 1 < |t| ^ 2 := by nlinarith
      nlinarith [ha2]
    linarith

lemma sinc_pi_fourth_integrable : Integrable (fun ξ : ℝ => Real.sinc (π * ξ) ^ 4) := by
  have hg : Integrable (fun ξ : ℝ => 2 * (1 + ξ ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul 2
  apply Integrable.mono' hg
  · exact ((Real.continuous_sinc.comp
      (continuous_const.mul continuous_id)).pow 4).aestronglyMeasurable
  · filter_upwards with ξ
    have h1 := abs_sinc_pow_four_le (π * ξ)
    have h2 : 2 * (1 + (π * ξ) ^ 2)⁻¹ ≤ 2 * (1 + ξ ^ 2)⁻¹ := by
      have hp : (1:ℝ) ≤ π ^ 2 := by nlinarith [Real.pi_gt_three]
      have hle : (1:ℝ) + ξ ^ 2 ≤ 1 + (π * ξ) ^ 2 := by
        nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ π ^ 2 - 1) (sq_nonneg ξ)]
      have h3 : (0:ℝ) < 1 + ξ ^ 2 := by positivity
      gcongr
    simp only [Real.norm_eq_abs]
    linarith

theorem integral_sinc_pi_fourth : ∫ ξ : ℝ, Real.sinc (π * ξ) ^ 4 = 2 / 3 := by
  have hFint : Integrable (𝓕 gg) := by
    have : (𝓕 gg) = fun ξ : ℝ => ((Real.sinc (π * ξ) ^ 4 : ℝ) : ℂ) := funext fourier_gg
    rw [this]
    exact sinc_pi_fourth_integrable.ofReal
  have hinv : 𝓕⁻ (𝓕 gg) 0 = gg 0 :=
    gg_integrable.fourierInv_fourier_eq hFint gg_continuous.continuousAt
  have hL : 𝓕⁻ (𝓕 gg) 0 = ∫ ξ : ℝ, ((Real.sinc (π * ξ) ^ 4 : ℝ) : ℂ) := by
    rw [Real.fourierInv_eq]
    simp only [inner_zero_right, fourier_gg]
    simp
  rw [hL, gg_zero, integral_complex_ofReal] at hinv
  have := congrArg Complex.re hinv
  simpa using this

/-- `∫_ℝ (sin x / x)^4 dx = 2π/3`. -/
theorem integral_sinc_fourth : ∫ x : ℝ, (Real.sin x / x) ^ 4 = 2 * π / 3 := by
  have h1 : ∫ ξ : ℝ, Real.sinc (π * ξ) ^ 4 = |π⁻¹| • ∫ x : ℝ, Real.sinc x ^ 4 :=
    Measure.integral_comp_mul_left (fun x => Real.sinc x ^ 4) π
  rw [integral_sinc_pi_fourth, abs_of_pos (by positivity : (0:ℝ) < π⁻¹), smul_eq_mul] at h1
  have h2 : ∫ x : ℝ, Real.sinc x ^ 4 = 2 * π / 3 := by
    have hpi : (π : ℝ) ≠ 0 := Real.pi_ne_zero
    field_simp at h1
    linarith
  rw [← h2]
  apply integral_congr_ae
  filter_upwards [compl_mem_ae_iff.2 (Real.volume_singleton (a := (0:ℝ)))] with x hx
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hx
  rw [Real.sinc_of_ne_zero hx]

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

