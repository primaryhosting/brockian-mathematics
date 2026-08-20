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
