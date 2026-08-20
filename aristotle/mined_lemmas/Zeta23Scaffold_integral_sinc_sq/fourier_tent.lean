import Mathlib
/-!
# Integral Sinc Sq
Category: C Integral
Target: Zeta23Scaffold.integral_sinc_sq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Real Complex
open scoped FourierTransform

noncomputable section

namespace Zeta23Scaffold

/-- The tent function `t ↦ max (1 - |t|) 0`. -/

lemma fourier_tent (ξ : ℝ) : 𝓕 tent ξ = ((Real.sinc (π * ξ) ^ 2 : ℝ) : ℂ) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have hrw : ∀ v : ℝ, Complex.exp ((↑(-2 * π * v * ξ)) * I) • tent v
      = Complex.exp ((↑((-2 * π * ξ) * v)) * I) * tent v := by
    intro v
    rw [smul_eq_mul]
    ring_nf
  simp_rw [hrw]
  rw [integral_tent_mul, tent_fourier_aux]
  rw [Complex.ofReal_inj]
  rcases eq_or_ne ξ 0 with rfl | hξ
  · simp only [Real.sinc_zero, mul_zero, one_pow, zero_mul, Real.cos_zero, mul_one]
    rw [intervalIntegral.integral_sub intervalIntegrable_const
      intervalIntegral.intervalIntegrable_id]
    norm_num
  · have ha : (-2 * π * ξ) ≠ 0 := by
      have := Real.pi_ne_zero
      simp only [ne_eq, mul_eq_zero, not_or]
      push_neg
      exact ⟨⟨by norm_num, this⟩, hξ⟩
    rw [real_tent_cos _ ha]
    have hpi : π * ξ ≠ 0 := mul_ne_zero Real.pi_ne_zero hξ
    rw [Real.sinc_of_ne_zero hpi]
    have hc : Real.cos (-2 * π * ξ) = 1 - 2 * Real.sin (π * ξ) ^ 2 := by
      rw [show (-2 * π * ξ) = -(2 * (π * ξ)) by ring, Real.cos_neg, Real.cos_two_mul']
      nlinarith [Real.sin_sq_add_cos_sq (π * ξ)]
    rw [hc]
    field_simp
    ring

