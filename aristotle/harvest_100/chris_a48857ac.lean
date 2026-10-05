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

The normalization integral of the sine kernel,
`∫ x : ℝ, (sin x / x) ^ 2 = π`.

The proof computes the Fourier transform of the triangle function
`tri x = max (1 - |x|) 0`, which is `w ↦ sinc (π w) ^ 2`, and then applies the
Fourier inversion formula at `0`.

Note that in Lean `sin 0 / 0 = 0`, so the integrand of the main statement differs from the
continuous extension `sinc` only on the null set `{0}`; the value of the integral is unaffected.
-/

open MeasureTheory Real Complex
open scoped FourierTransform

namespace Zeta23Scaffold

/-- The triangle function `x ↦ max (1 - |x|) 0`, viewed as a complex-valued function on `ℝ`. -/
noncomputable def tri (x : ℝ) : ℂ := ((max (1 - |x|) 0 : ℝ) : ℂ)

lemma tri_continuous : Continuous tri := by
  unfold tri; fun_prop

lemma tri_eq_zero {x : ℝ} (hx : 1 ≤ |x|) : tri x = 0 := by
  simp [tri, sub_nonpos.2 hx]

lemma tri_zero : tri 0 = 1 := by simp [tri]

lemma tri_integrable : Integrable tri := by
  have hsupp : Function.support tri ⊆ Set.Icc (-1) 1 := by
    intro x hx
    simp only [Function.mem_support] at hx
    by_contra h
    refine hx (tri_eq_zero ?_)
    simp only [Set.mem_Icc, not_and_or, not_le] at h
    rcases h with h | h
    · rw [le_abs]; right; linarith
    · rw [le_abs]; left; linarith
  exact tri_continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsupp)

/-- `sinc ^ 2` is integrable on `ℝ`: it is bounded by `2 / (1 + x ^ 2)`. -/
lemma integrable_sinc_sq : Integrable (fun x : ℝ => Real.sinc x ^ 2) := by
  have hg : Integrable (fun x : ℝ => 2 * (1 + x ^ 2)⁻¹) := integrable_inv_one_add_sq.const_mul 2
  refine Integrable.mono' hg (by fun_prop) (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_pow, sq_abs]
  rcases le_or_gt |x| 1 with h | h
  · have h1 : Real.sinc x ^ 2 ≤ 1 := by
      nlinarith [abs_le.1 (Real.abs_sinc_le_one x)]
    have h2 : x ^ 2 ≤ 1 := by nlinarith [sq_abs x, abs_nonneg x]
    have : (1:ℝ) ≤ 2 * (1 + x ^ 2)⁻¹ := by
      rw [le_mul_inv_iff₀ (by positivity)]; linarith
    linarith
  · have hx : x ≠ 0 := by rintro rfl; simp at h; linarith
    have hs : Real.sinc x ^ 2 ≤ (x ^ 2)⁻¹ := by
      rw [Real.sinc_of_ne_zero hx, div_pow]
      have : Real.sin x ^ 2 ≤ 1 := by nlinarith [Real.neg_one_le_sin x, Real.sin_le_one x]
      rw [div_le_iff₀ (by positivity), inv_mul_cancel₀ (by positivity)]
      exact this
    have h2 : 1 < x ^ 2 := by nlinarith [sq_abs x]
    have : (x ^ 2)⁻¹ ≤ 2 * (1 + x ^ 2)⁻¹ := by
      rw [inv_le_iff_one_le_mul₀ (by positivity), mul_comm, ← mul_assoc,
        le_mul_inv_iff₀ (by positivity)]
      linarith
    linarith

/-- Splitting the integral of `exp (c * v) * tri v` into the two halves of the triangle. -/
lemma integral_exp_mul_tri (c : ℂ) :
    ∫ v : ℝ, Complex.exp (c * v) * tri v
      = (∫ v in (-1:ℝ)..0, (1 + (v:ℂ)) * Complex.exp (c * v))
        + ∫ v in (0:ℝ)..1, (1 - (v:ℂ)) * Complex.exp (c * v) := by
  have hcont : Continuous (fun v : ℝ => Complex.exp (c * v) * tri v) :=
    (by fun_prop : Continuous (fun v : ℝ => Complex.exp (c * v))).mul tri_continuous
  have h1 : ∫ v : ℝ, Complex.exp (c * v) * tri v
      = ∫ v in Set.Ioc (-1:ℝ) 1, Complex.exp (c * v) * tri v := by
    rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro x hx
    simp only [Set.mem_Ioc, not_and_or, not_lt, not_le] at hx
    rw [tri_eq_zero ?_, mul_zero]
    rcases hx with h | h
    · rw [le_abs]; right; linarith
    · rw [le_abs]; left; linarith
  rw [h1, ← intervalIntegral.integral_of_le (by norm_num : (-1:ℝ) ≤ 1),
    ← intervalIntegral.integral_add_adjacent_intervals
      (a := (-1:ℝ)) (b := 0) (c := 1) (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)]
  congr 1
  · refine intervalIntegral.integral_congr fun x hx => ?_
    rw [Set.uIcc_of_le (by norm_num : (-1:ℝ) ≤ 0)] at hx
    simp only [Set.mem_Icc] at hx
    simp only [tri, abs_of_nonpos hx.2, mul_comm]
    rw [max_eq_left (by linarith)]
    push_cast
    ring
  · refine intervalIntegral.integral_congr fun x hx => ?_
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hx
    simp only [Set.mem_Icc] at hx
    simp only [tri, abs_of_nonneg hx.1, mul_comm]
    rw [max_eq_left (by linarith)]
    push_cast
    ring

private lemma hasDerivAt_cexp_mul (c : ℂ) (x : ℝ) :
    HasDerivAt (fun x : ℝ => Complex.exp (c * x)) (c * Complex.exp (c * x)) x := by
  have h1 : HasDerivAt (fun x : ℝ => c * (x:ℂ)) c x := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).const_mul c
  simpa [mul_comm] using h1.cexp

lemma integral_right_half (c : ℂ) (hc : c ≠ 0) :
    ∫ v in (0:ℝ)..1, (1 - (v:ℂ)) * Complex.exp (c * v)
      = Complex.exp c / c ^ 2 - 1 / c - 1 / c ^ 2 := by
  have key : ∀ x : ℝ, HasDerivAt (fun x : ℝ => (1 - (x:ℂ)) * Complex.exp (c * x) / c
      + Complex.exp (c * x) / c ^ 2) ((1 - (x:ℂ)) * Complex.exp (c * x)) x := by
    intro x
    have he := hasDerivAt_cexp_mul c x
    have h2 : HasDerivAt (fun x : ℝ => (1 - (x:ℂ))) (-1) x := by
      simpa using ((Complex.ofRealCLM.hasDerivAt (x := x)).const_sub 1)
    have := ((h2.mul he).div_const c).add (he.div_const (c ^ 2))
    convert this using 1
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => key x)]
  · push_cast
    field_simp
    norm_num
    ring
  · exact (Continuous.intervalIntegrable (by fun_prop) _ _)

lemma integral_left_half (c : ℂ) (hc : c ≠ 0) :
    ∫ v in (-1:ℝ)..0, (1 + (v:ℂ)) * Complex.exp (c * v)
      = 1 / c - 1 / c ^ 2 + Complex.exp (-c) / c ^ 2 := by
  have key : ∀ x : ℝ, HasDerivAt (fun x : ℝ => (1 + (x:ℂ)) * Complex.exp (c * x) / c
      - Complex.exp (c * x) / c ^ 2) ((1 + (x:ℂ)) * Complex.exp (c * x)) x := by
    intro x
    have he := hasDerivAt_cexp_mul c x
    have h2 : HasDerivAt (fun x : ℝ => (1 + (x:ℂ))) 1 x := by
      simpa using ((Complex.ofRealCLM.hasDerivAt (x := x)).const_add 1)
    have := ((h2.mul he).div_const c).sub (he.div_const (c ^ 2))
    convert this using 1
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => key x)]
  · push_cast
    field_simp
    norm_num
  · exact (Continuous.intervalIntegrable (by fun_prop) _ _)

/-- The Fourier transform of the triangle function is `w ↦ sinc (π w) ^ 2`. -/
lemma fourier_tri (w : ℝ) : 𝓕 tri w = ((Real.sinc (π * w) ^ 2 : ℝ) : ℂ) := by
  have hrw : 𝓕 tri w = ∫ v : ℝ, Complex.exp ((-(2 * π * w : ℝ) * Complex.I) * v) * tri v := by
    rw [Real.fourier_real_eq]
    simp only [Real.fourierChar_apply, Circle.smul_def, smul_eq_mul]
    congr 1 with v
    congr 2
    push_cast
    ring
  rw [hrw, integral_exp_mul_tri]
  rcases eq_or_ne w 0 with rfl | hw
  · have e1 : ∫ v in (-1:ℝ)..0, (1 + (v:ℂ)) * Complex.exp ((-(2*π*0 : ℝ) * Complex.I) * v)
        = ((∫ v in (-1:ℝ)..0, (1 + v) : ℝ) : ℂ) := by
      rw [← intervalIntegral.integral_ofReal]
      refine intervalIntegral.integral_congr fun x _ => ?_
      push_cast
      simp
    have e2 : ∫ v in (0:ℝ)..1, (1 - (v:ℂ)) * Complex.exp ((-(2*π*0 : ℝ) * Complex.I) * v)
        = ((∫ v in (0:ℝ)..1, (1 - v) : ℝ) : ℂ) := by
      rw [← intervalIntegral.integral_ofReal]
      refine intervalIntegral.integral_congr fun x _ => ?_
      push_cast
      simp
    rw [e1, e2]
    have h1 : ∫ v in (-1:ℝ)..0, (1 + v) = (1:ℝ)/2 := by
      rw [intervalIntegral.integral_add intervalIntegrable_const
        intervalIntegral.intervalIntegrable_id]
      norm_num
    have h2 : ∫ v in (0:ℝ)..1, (1 - v) = (1:ℝ)/2 := by
      rw [intervalIntegral.integral_sub intervalIntegrable_const
        intervalIntegral.intervalIntegrable_id]
      norm_num
    rw [h1, h2]
    norm_num
  · set c : ℂ := -(2 * π * w : ℝ) * Complex.I with hcdef
    have hpi := Real.pi_ne_zero
    have hpw : (π * w) ≠ 0 := mul_ne_zero hpi hw
    have hc : c ≠ 0 := by
      rw [hcdef]
      refine mul_ne_zero ?_ Complex.I_ne_zero
      simp only [neg_ne_zero, ne_eq, Complex.ofReal_eq_zero]
      exact mul_ne_zero (mul_ne_zero two_ne_zero hpi) hw
    rw [integral_left_half c hc, integral_right_half c hc]
    have hsum : (1 / c - 1 / c ^ 2 + Complex.exp (-c) / c ^ 2)
        + (Complex.exp c / c ^ 2 - 1 / c - 1 / c ^ 2)
        = (Complex.exp c + Complex.exp (-c) - 2) / c ^ 2 := by
      field_simp
      ring
    rw [hsum]
    have hcos : Complex.exp c + Complex.exp (-c) = 2 * (Real.cos (2 * π * w) : ℂ) := by
      rw [hcdef, Complex.ofReal_cos, Complex.cos]
      ring_nf
    have hcsq : c ^ 2 = -(((2 * π * w : ℝ)) : ℂ) ^ 2 := by
      rw [hcdef]; ring_nf; simp [Complex.I_sq]
    have h2 : (Real.cos (2 * π * w) : ℂ) = 1 - 2 * (Real.sin (π * w) : ℂ) ^ 2 := by
      have h : Real.cos (2 * π * w) = 1 - 2 * Real.sin (π * w) ^ 2 := by
        have h1 := Real.cos_two_mul (π * w)
        have h2 := Real.sin_sq_add_cos_sq (π * w)
        rw [show 2 * π * w = 2 * (π * w) by ring, h1]; nlinarith
      rw [h]; push_cast; ring
    rw [Real.sinc_of_ne_zero hpw, hcos, hcsq, h2]
    push_cast
    field_simp
    ring

/-- The Fourier transform of the triangle function is integrable. -/
lemma integrable_fourier_tri : Integrable (𝓕 tri) := by
  have h : 𝓕 tri = fun w : ℝ => ((Real.sinc (π * w) ^ 2 : ℝ) : ℂ) := funext fun w => fourier_tri w
  rw [h]
  exact (integrable_sinc_sq.comp_mul_left' Real.pi_ne_zero).ofReal

lemma integral_sinc_pi_mul_sq : ∫ w : ℝ, Real.sinc (π * w) ^ 2 = 1 := by
  have hinv := tri_integrable.fourierInv_fourier_eq (v := (0:ℝ)) integrable_fourier_tri
    (tri_continuous.continuousAt)
  rw [Real.fourierInv_eq, tri_zero] at hinv
  simp only [inner_zero_right, AddChar.map_zero_eq_one, one_smul, fourier_tri] at hinv
  rw [integral_complex_ofReal] at hinv
  exact_mod_cast hinv

/-- The normalization integral of the sine kernel: `∫ x : ℝ, (sin x / x) ^ 2 = π`. -/
theorem integral_sinc_sq : ∫ x : ℝ, (Real.sin x / x) ^ 2 = π := by
  have hae : (fun x : ℝ => (Real.sin x / x) ^ 2) =ᵐ[volume] fun x : ℝ => Real.sinc x ^ 2 := by
    have h0 : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by
      rw [MeasureTheory.ae_iff]
      simp
    filter_upwards [h0] with x hx
    rw [Real.sinc_of_ne_zero hx]
  rw [MeasureTheory.integral_congr_ae hae]
  have hchange : ∫ w : ℝ, Real.sinc (π * w) ^ 2 = |π⁻¹| • ∫ x : ℝ, Real.sinc x ^ 2 :=
    MeasureTheory.Measure.integral_comp_mul_left (fun x => Real.sinc x ^ 2) π
  rw [integral_sinc_pi_mul_sq, abs_of_pos (by positivity : (0:ℝ) < π⁻¹), smul_eq_mul] at hchange
  field_simp at hchange
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

