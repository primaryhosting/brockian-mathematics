import Mathlib

/-!
# Integral Sinc Sq
Category: C Integral
Target: Zeta23Scaffold.integral_sinc_sq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Complex Real
open scoped FourierTransform

namespace Zeta23Scaffold

/-- The triangle ("tent") function `x ↦ max (1 - |x|) 0`, viewed as a complex-valued function. -/

lemma fourier_tri_of_ne_zero {w : ℝ} (hw : w ≠ 0) :
    𝓕 tri w = ((Real.sin (π * w) / (π * w)) ^ 2 : ℝ) := by
  set t : ℝ := π * w with ht
  have hts : t ≠ 0 := mul_ne_zero Real.pi_ne_zero hw
  set c : ℂ := ((-2 * t : ℝ) : ℂ) * I with hcdef
  have hc : c ≠ 0 := by simp [hcdef, Complex.ext_iff, hts]
  have h1 : 𝓕 tri w = ∫ v : ℝ, Complex.exp (c * v) * tri v := by
    rw [Real.fourier_real_eq_integral_exp_smul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only [smul_eq_mul]
    congr 2
    rw [hcdef, ht]
    push_cast
    ring
  rw [h1, integral_tri_exp c hc, hcdef]
  have hcos : Complex.exp ((-2 * t : ℝ) * I) + Complex.exp (-((-2 * t : ℝ) * I))
      = 2 * (Real.cos (2 * t) : ℂ) := by
    rw [Complex.ofReal_cos, Complex.cos]
    push_cast
    ring_nf
  rw [hcos]
  have h2 : Real.cos (2 * t) = 1 - 2 * Real.sin t ^ 2 := by
    rw [Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq t]
  rw [h2]
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hts
  push_cast
  field_simp
  ring_nf
  simp [Complex.I_sq]

