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
-/

open MeasureTheory Complex intervalIntegral
open scoped FourierTransform Real

namespace Zeta23Scaffold

/-! ## Overview

We prove `∫ x : ℝ, (sin x / x) ^ 4 = 2 π / 3`.

The strategy is the Fourier multiplication formula `∫ 𝓕 f · g = ∫ f · 𝓕 g`.
Let `T` be the tent function `T x = max (1 - π |x|) 0`, supported in `[-1/π, 1/π]`.
An explicit computation gives `𝓕 T ξ = sinc(ξ)^2 / π =: S ξ`, and Fourier inversion
gives `𝓕 S = T` (both `T` and `S` are integrable, `T` is continuous, and `S` is even).
Hence `∫ S^2 = ∫ 𝓕 T · S = ∫ T · 𝓕 S = ∫ T^2 = 2/(3π)`, and since
`S^2 = sinc^4 / π^2` we get `∫ sinc^4 = 2π/3`.
-/

/-- The "tent" function `x ↦ max (1 - π|x|) 0`, supported on `[-1/π, 1/π]`. -/
noncomputable def tent (x : ℝ) : ℝ := max (1 - π * |x|) 0

/-- The tent function, complex valued. -/
noncomputable def tentC (x : ℝ) : ℂ := (tent x : ℝ)

/-- `x ↦ sinc(x)^2 / π`, which is the Fourier transform of the tent function. -/
noncomputable def sincSq (x : ℝ) : ℝ := Real.sinc x ^ 2 / π

/-- `x ↦ sinc(x)^2 / π`, complex valued. -/
noncomputable def sincSqC (x : ℝ) : ℂ := (sincSq x : ℝ)

/-! ### Generic auxiliary computations -/

/-- A function vanishing outside `[-a, a]` has the same integral as on the interval. -/
theorem integral_eq_interval {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) {a : ℝ} (ha : 0 ≤ a) (hf : ∀ x, a ≤ |x| → f x = 0) :
    ∫ x : ℝ, f x = ∫ x in (-a)..a, f x := by
  rw [intervalIntegral.integral_of_le (by linarith)]
  refine (setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => hf x ?_)).symm
  simp only [Set.mem_Ioc, not_and_or, not_lt, not_le] at hx
  rcases hx with h | h
  · rw [abs_of_nonpos (by linarith)]; linarith
  · rw [abs_of_nonneg (by linarith)]; linarith

theorem integral_lin (A B u v : ℝ) :
    ∫ x in u..v, (A + B * x) = (A * v + B * v ^ 2 / 2) - (A * u + B * u ^ 2 / 2) := by
  apply integral_eq_sub_of_hasDerivAt
  · intro x _
    have h : HasDerivAt (fun x : ℝ => A * x + B * x ^ 2 / 2) (A + B * x) x := by
      have h1 : HasDerivAt (fun x : ℝ => A * x) A x := by
        simpa using (hasDerivAt_id x).const_mul A
      have h2 : HasDerivAt (fun x : ℝ => B * x ^ 2 / 2) (B * x) x := by
        have := (((hasDerivAt_pow 2 x).const_mul B).div_const 2)
        convert this using 1
        push_cast; ring
      simpa using h1.add h2
    convert h using 1
  · exact Continuous.intervalIntegrable (by fun_prop) _ _

theorem integral_lin_sq (A B u v : ℝ) (hB : B ≠ 0) :
    ∫ x in u..v, (A + B * x) ^ 2 = (A + B * v) ^ 3 / (3 * B) - (A + B * u) ^ 3 / (3 * B) := by
  apply integral_eq_sub_of_hasDerivAt
  · intro x _
    have h1 : HasDerivAt (fun x : ℝ => A + B * x) B x := by
      simpa using ((hasDerivAt_id x).const_mul B).const_add A
    have h := (h1.pow 3).div_const (3 * B)
    convert h using 1
    field_simp
    ring
  · exact Continuous.intervalIntegrable (by fun_prop) _ _

/-! ### Elementary properties of the tent function -/

theorem continuous_tent : Continuous tent := by
  unfold tent; fun_prop

theorem continuous_tentC : Continuous tentC := by
  unfold tentC; exact Complex.continuous_ofReal.comp continuous_tent

theorem tent_neg (x : ℝ) : tent (-x) = tent x := by
  simp [tent]

theorem tent_zero_of_le {x : ℝ} (hx : 1 / π ≤ |x|) : tent x = 0 := by
  have hπ : 0 < π := Real.pi_pos
  rw [div_le_iff₀ hπ] at hx
  simp [tent, max_eq_right (by nlinarith : 1 - π * |x| ≤ 0)]

theorem tent_pos_part {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / π) : tent x = 1 - π * x := by
  have hπ : 0 < π := Real.pi_pos
  rw [le_div_iff₀ hπ] at hx
  simp [tent, abs_of_nonneg hx0, max_eq_left (by nlinarith : (0:ℝ) ≤ 1 - π * x)]

theorem tent_neg_part {x : ℝ} (hx0 : x ≤ 0) (hx : -(1 / π) ≤ x) : tent x = 1 + π * x := by
  have hπ : 0 < π := Real.pi_pos
  rw [neg_le, le_div_iff₀ hπ] at hx
  rw [tent, abs_of_nonpos hx0, max_eq_left (by nlinarith : (0:ℝ) ≤ 1 - π * -x)]
  ring

theorem hasCompactSupport_tentC : HasCompactSupport tentC := by
  apply HasCompactSupport.intro (isCompact_Icc (a := -(1 / π)) (b := 1 / π))
  intro x hx
  simp only [Set.mem_Icc, not_and_or, not_le] at hx
  have h : 1 / π ≤ |x| := by
    rcases hx with h | h
    · rw [abs_of_nonpos (by nlinarith [Real.pi_pos, one_div_pos.mpr Real.pi_pos] : x ≤ 0)]
      linarith
    · rw [abs_of_nonneg (by nlinarith [Real.pi_pos, one_div_pos.mpr Real.pi_pos] : (0:ℝ) ≤ x)]
      linarith
  simp [tentC, tent_zero_of_le h]

theorem integrable_tentC : Integrable tentC :=
  continuous_tentC.integrable_of_hasCompactSupport hasCompactSupport_tentC

/-! ### Integrability of `sincSq` -/

theorem sinc_sq_mul_le (x : ℝ) : Real.sinc x ^ 2 * (1 + x ^ 2) ≤ 2 := by
  have h1 : Real.sinc x ^ 2 ≤ 1 := by
    have := Real.abs_sinc_le_one x
    nlinarith [abs_nonneg (Real.sinc x), sq_abs (Real.sinc x)]
  have h2 : x ^ 2 * Real.sinc x ^ 2 = Real.sin x ^ 2 := by
    rcases eq_or_ne x 0 with rfl | h
    · simp
    · rw [Real.sinc_of_ne_zero h]; field_simp
  nlinarith [Real.sin_sq_le_one x]

theorem integrable_sincSq : Integrable sincSq := by
  have hπ : 0 < π := Real.pi_pos
  apply Integrable.mono' (g := fun x : ℝ => (2 / π) * (1 + x ^ 2)⁻¹)
    (integrable_inv_one_add_sq.const_mul _)
  · exact (Real.continuous_sinc.pow 2 |>.div_const π).aestronglyMeasurable
  · filter_upwards with x
    have hpos : (0:ℝ) < 1 + x ^ 2 := by positivity
    rw [Real.norm_eq_abs, sincSq, abs_of_nonneg (by positivity : (0:ℝ) ≤ Real.sinc x ^ 2 / π)]
    have h2 : Real.sinc x ^ 2 ≤ 2 / (1 + x ^ 2) := (le_div_iff₀ hpos).mpr (sinc_sq_mul_le x)
    have h3 : (2 / π) * (1 + x ^ 2)⁻¹ = (2 / (1 + x ^ 2)) / π := by field_simp
    rw [h3]
    gcongr

theorem integrable_sincSqC : Integrable sincSqC :=
  Integrable.ofReal integrable_sincSq

/-! ### The Fourier transform of the tent function -/

/-- An antiderivative of `x ↦ exp (-c x i) (A + B x)`. -/
noncomputable def antider (c A B : ℝ) (t : ℝ) : ℂ :=
  Complex.exp (-((c : ℂ) * t) * I) * ((I * A / c + B / (c : ℂ) ^ 2) + (I * B / c) * t)

theorem hasDerivAt_antider (c A B : ℝ) (hc : c ≠ 0) (x : ℝ) :
    HasDerivAt (antider c A B) (Complex.exp (-((c : ℂ) * x) * I) * (A + B * x)) x := by
  have h1 : HasDerivAt (fun t : ℝ => (-((c : ℂ) * t) * I)) (-(c : ℂ) * I) x := by
    have : HasDerivAt (fun t : ℝ => ((t : ℂ))) 1 x := Complex.ofRealCLM.hasDerivAt
    simpa using ((this.const_mul (-(c : ℂ))).mul_const I)
  have h2 := h1.cexp
  have h3 : HasDerivAt (fun t : ℝ => ((I * A / c + B / (c : ℂ) ^ 2) + (I * B / c) * t))
      (I * B / c) x := by
    have : HasDerivAt (fun t : ℝ => ((t : ℂ))) 1 x := Complex.ofRealCLM.hasDerivAt
    simpa using ((this.const_mul (I * B / (c : ℂ))).const_add ((I * A / c + B / (c : ℂ) ^ 2)))
  have hcc : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc
  have h := h2.mul h3
  convert h using 1
  field_simp
  ring_nf
  simp [Complex.I_sq]

theorem integral_exp_lin (c A B u v : ℝ) (hc : c ≠ 0) :
    ∫ x in u..v, Complex.exp (-((c : ℂ) * x) * I) * ((A : ℂ) + B * x) =
      antider c A B v - antider c A B u := by
  apply integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_antider c A B hc x)
  exact Continuous.intervalIntegrable (by fun_prop) _ _

theorem integral_tent : ∫ x : ℝ, tent x = 1 / π := by
  have hπ : 0 < π := Real.pi_pos
  have hcont : Continuous tent := continuous_tent
  rw [integral_eq_interval _ (by positivity : (0:ℝ) ≤ 1 / π) (fun x hx => tent_zero_of_le hx),
    ← intervalIntegral.integral_add_adjacent_intervals (b := 0)
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)]
  have hle : -(1 / π) ≤ (0:ℝ) := neg_nonpos.mpr (by positivity)
  have h1 : ∫ x in (-(1 / π))..(0:ℝ), tent x = 1 / (2 * π) := by
    rw [intervalIntegral.integral_congr (g := fun x : ℝ => 1 + π * x) (fun x hx => by
      rw [Set.uIcc_of_le hle] at hx
      exact tent_neg_part hx.2 hx.1), integral_lin]
    field_simp
    ring
  have h2 : ∫ x in (0:ℝ)..(1 / π), tent x = 1 / (2 * π) := by
    rw [intervalIntegral.integral_congr (g := fun x : ℝ => 1 + (-π) * x) (fun x hx => by
      rw [Set.uIcc_of_le (by positivity : (0:ℝ) ≤ 1 / π)] at hx
      rw [tent_pos_part hx.1 hx.2]; ring), integral_lin]
    field_simp
    ring
  rw [h1, h2]
  field_simp
  ring

theorem fourier_tentC : 𝓕 tentC = sincSqC := by
  have hπ : 0 < π := Real.pi_pos
  have hπ' : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  funext ξ
  rcases eq_or_ne ξ 0 with rfl | hξ
  · -- at `0` the Fourier transform is just the total integral of the tent
    have h : 𝓕 tentC 0 = ∫ v : ℝ, tentC v := by
      rw [Real.fourier_real_eq_integral_exp_smul]
      congr 1
      funext v
      norm_num
    rw [h]
    have : ∫ v : ℝ, tentC v = ((∫ v : ℝ, tent v : ℝ) : ℂ) := integral_complex_ofReal
    rw [this, integral_tent]
    simp [sincSqC, sincSq, Real.sinc_zero]
  · have hξ' : (ξ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hξ
    set c : ℝ := 2 * π * ξ with hc
    have hcne : c ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) hξ
    have step1 : 𝓕 tentC ξ = ∫ v : ℝ, Complex.exp (-((c : ℂ) * v) * I) * tentC v := by
      rw [Real.fourier_real_eq_integral_exp_smul]
      congr 1
      funext v
      rw [smul_eq_mul]
      congr 2
      push_cast [hc]
      ring
    have hcont : Continuous (fun v : ℝ => Complex.exp (-((c : ℂ) * v) * I) * tentC v) := by
      unfold tentC tent; fun_prop
    rw [step1, integral_eq_interval _ (by positivity : (0:ℝ) ≤ 1 / π)
        (by intro x hx; simp [tentC, tent_zero_of_le hx]),
      ← intervalIntegral.integral_add_adjacent_intervals (b := 0)
        (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)]
    have hle : -(1 / π) ≤ (0:ℝ) := neg_nonpos.mpr (by positivity)
    have h1 : ∫ v in (-(1 / π))..(0:ℝ), Complex.exp (-((c : ℂ) * v) * I) * tentC v
        = antider c 1 π 0 - antider c 1 π (-(1 / π)) := by
      rw [← integral_exp_lin c 1 π _ _ hcne]
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le hle] at hx
      simp only [tentC, tent_neg_part hx.2 hx.1]
      push_cast
      ring
    have h2 : ∫ v in (0:ℝ)..(1 / π), Complex.exp (-((c : ℂ) * v) * I) * tentC v
        = antider c 1 (-π) (1 / π) - antider c 1 (-π) 0 := by
      rw [← integral_exp_lin c 1 (-π) _ _ hcne]
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le (by positivity : (0:ℝ) ≤ 1 / π)] at hx
      simp only [tentC, tent_pos_part hx.1 hx.2]
      push_cast
      ring
    rw [h1, h2]
    -- explicit evaluation of the antiderivatives
    have hval : sincSqC ξ = ((Real.sin ξ : ℂ)) ^ 2 / ((π : ℂ) * (ξ : ℂ) ^ 2) := by
      rw [sincSqC, sincSq, Real.sinc_of_ne_zero hξ]
      push_cast
      field_simp
    have hcos : Real.cos (2 * ξ) = 1 - 2 * Real.sin ξ ^ 2 := by
      rw [Real.cos_two_mul]
      nlinarith [Real.sin_sq_add_cos_sq ξ]
    unfold antider
    rw [hc]
    push_cast
    rw [show -((2 * (π : ℂ) * ξ) * -(1 / π)) * I = ((2 * ξ : ℝ) : ℂ) * I by push_cast; field_simp,
      show -((2 * (π : ℂ) * ξ) * (1 / π)) * I = ((-(2 * ξ) : ℝ) : ℂ) * I by push_cast; field_simp,
      show -((2 * (π : ℂ) * ξ) * 0) * I = ((0 : ℝ) : ℂ) * I by push_cast; ring]
    rw [Complex.exp_mul_I, Complex.exp_mul_I, Complex.exp_mul_I,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin, hval]
    simp only [Real.cos_neg, Real.sin_neg, Real.cos_zero, Real.sin_zero, hcos]
    push_cast
    field_simp
    ring

theorem fourier_sincSqC : 𝓕 sincSqC = tentC := by
  have h : 𝓕⁻ (𝓕 tentC) = tentC :=
    continuous_tentC.fourierInv_fourier_eq integrable_tentC
      (by rw [fourier_tentC]; exact integrable_sincSqC)
  rw [fourier_tentC] at h
  funext x
  have h2 : 𝓕⁻ sincSqC (-x) = 𝓕 sincSqC x := by
    rw [Real.fourierInv_eq_fourier_neg, neg_neg]
  rw [← h2, h]
  simp [tentC, tent_neg]

/-! ### The multiplication formula -/

theorem integral_fourier_mul (f g : ℝ → ℂ) (hf : Integrable f) (hg : Integrable g) :
    ∫ ξ : ℝ, 𝓕 f ξ * g ξ = ∫ x : ℝ, f x * 𝓕 g x := by
  have hflip : (innerₗ ℝ).flip = innerₗ ℝ := by ext; simp
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip (𝕜 := ℝ) (V := ℝ) (W := ℝ)
    (e := Real.fourierChar) (μ := volume) (ν := volume) (L := innerₗ ℝ) (f := f) (g := g)
    Real.continuous_fourierChar (by fun_prop) hf hg
  rw [hflip] at h
  simpa [smul_eq_mul] using h

/-! ### Putting things together -/

theorem integral_tent_sq : ∫ x : ℝ, tent x ^ 2 = 2 / (3 * π) := by
  have hπ : 0 < π := Real.pi_pos
  have hcont : Continuous fun x : ℝ => tent x ^ 2 := continuous_tent.pow 2
  have hz : ∀ x : ℝ, 1 / π ≤ |x| → tent x ^ 2 = 0 := by
    intro x hx
    simp [tent_zero_of_le hx]
  rw [integral_eq_interval _ (by positivity : (0:ℝ) ≤ 1 / π) hz,
    ← intervalIntegral.integral_add_adjacent_intervals (b := 0)
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)]
  have hle : -(1 / π) ≤ (0:ℝ) := neg_nonpos.mpr (by positivity)
  have h1 : ∫ x in (-(1 / π))..(0:ℝ), tent x ^ 2 = 1 / (3 * π) := by
    rw [intervalIntegral.integral_congr (g := fun x : ℝ => (1 + π * x) ^ 2) (fun x hx => by
      rw [Set.uIcc_of_le hle] at hx
      rw [tent_neg_part hx.2 hx.1]), integral_lin_sq 1 π _ _ (ne_of_gt hπ)]
    field_simp
    norm_num
  have h2 : ∫ x in (0:ℝ)..(1 / π), tent x ^ 2 = 1 / (3 * π) := by
    rw [intervalIntegral.integral_congr (g := fun x : ℝ => (1 + (-π) * x) ^ 2) (fun x hx => by
      rw [Set.uIcc_of_le (by positivity : (0:ℝ) ≤ 1 / π)] at hx
      rw [tent_pos_part hx.1 hx.2]; ring_nf),
      integral_lin_sq 1 (-π) _ _ (by simp [ne_of_gt hπ])]
    field_simp
    ring
  rw [h1, h2]
  ring

theorem integral_sincSq_sq : ∫ x : ℝ, sincSq x ^ 2 = 2 / (3 * π) := by
  have h := integral_fourier_mul tentC sincSqC integrable_tentC integrable_sincSqC
  rw [fourier_tentC, fourier_sincSqC] at h
  have hL : ∫ ξ : ℝ, sincSqC ξ * sincSqC ξ = ((∫ x : ℝ, sincSq x ^ 2 : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    congr 1
    funext x
    simp [sincSqC, sq]
  have hR : ∫ x : ℝ, tentC x * tentC x = ((∫ x : ℝ, tent x ^ 2 : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    congr 1
    funext x
    simp [tentC, sq]
  rw [hL, hR, integral_tent_sq] at h
  exact_mod_cast h

/-- **The integral of `(sin x / x) ^ 4` over the real line is `2 π / 3`.** -/
theorem integral_sinc_fourth : ∫ x : ℝ, (Real.sin x / x) ^ 4 = 2 * π / 3 := by
  have hπ : 0 < π := Real.pi_pos
  have hae : (fun x : ℝ => (Real.sin x / x) ^ 4) =ᵐ[volume] fun x : ℝ => Real.sinc x ^ 4 := by
    have h0 : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by
      rw [ae_iff]
      simp
    filter_upwards [h0] with x hx
    rw [Real.sinc_of_ne_zero hx]
  rw [integral_congr_ae hae]
  have hsq : (fun x : ℝ => sincSq x ^ 2) = fun x : ℝ => Real.sinc x ^ 4 / π ^ 2 := by
    funext x
    rw [sincSq, div_pow]
    ring_nf
  have h := integral_sincSq_sq
  rw [hsq, MeasureTheory.integral_div,
    div_eq_iff (by positivity : (π:ℝ) ^ 2 ≠ 0)] at h
  rw [h]
  field_simp

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

