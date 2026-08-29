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

open MeasureTheory Real FourierTransform intervalIntegral

/-! ## The tent function and its Fourier transform -/

/-- The tent (triangle) function, supported on `[-1, 1]`. -/

lemma fourier_tentC {ξ : ℝ} (hξ : ξ ≠ 0) : 𝓕 tentC ξ = ((Real.sinc (π * ξ) ^ 2 : ℝ) : ℂ) := by
  set F : ℝ → ℂ := fun v => Complex.exp (↑(-2 * π * v * ξ) * Complex.I) • tentC v with hF
  have hcF : Continuous F := by
    apply Continuous.smul _ continuous_tentC
    fun_prop
  have step1 : 𝓕 tentC ξ = ∫ v in Set.Ioc (-1:ℝ) 1, F v := by
    rw [Real.fourier_real_eq_integral_exp_smul,
      MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro x hx
    simp [hF, tentC, tent_eq_zero (one_le_abs_of_notMem_Ioc hx)]
  rw [step1, ← intervalIntegral.integral_of_le (by norm_num : (-1:ℝ) ≤ 1)]
  have step2 : ∫ v in (-1:ℝ)..1, F v = ∫ x in (0:ℝ)..1, (F (-x) + F x) := by
    have h1 : IntervalIntegrable (fun x => F (-x)) volume 0 1 :=
      (hcF.comp continuous_neg).intervalIntegrable _ _
    rw [intervalIntegral.integral_add h1 (hcF.intervalIntegrable _ _),
      intervalIntegral.integral_comp_neg F,
      ← intervalIntegral.integral_add_adjacent_intervals (a := (-1:ℝ)) (b := 0) (c := 1)
        (hcF.intervalIntegrable _ _) (hcF.intervalIntegrable _ _)]
    norm_num
  rw [step2]
  have step3 : ∀ x ∈ Set.uIcc (0:ℝ) 1,
      F (-x) + F x = ((2 * (1 - x) * Real.cos ((2 * π * ξ) * x) : ℝ) : ℂ) := by
    intro x hx
    rw [Set.uIcc_of_le (by norm_num)] at hx
    obtain ⟨h0, h1⟩ := hx
    have habs : |x| ≤ 1 := by rw [abs_of_nonneg h0]; exact h1
    have habs' : |(-x)| ≤ 1 := by rwa [abs_neg]
    simp only [hF, tentC, tent_of_mem habs, tent_of_mem habs', abs_neg, abs_of_nonneg h0,
      smul_eq_mul]
    push_cast
    rw [Complex.cos]
    ring_nf
  rw [intervalIntegral.integral_congr step3, intervalIntegral.integral_ofReal,
    integral_two_mul_one_sub_mul_cos (2 * π * ξ) (by positivity)]
  congr 1
  have hpξ : π * ξ ≠ 0 := by positivity
  rw [Real.sinc_of_ne_zero hpξ]
  have h2 : Real.cos (2 * π * ξ) = 1 - 2 * Real.sin (π * ξ) ^ 2 := by
    have h3 : (2:ℝ) * π * ξ = 2 * (π * ξ) := by ring
    rw [h3, Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq (π * ξ)]
  rw [h2, div_pow]
  field_simp
  ring

/-! ## Integrability of `sinc²` -/

