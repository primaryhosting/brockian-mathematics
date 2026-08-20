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

The Dirichlet-type integral `∫_ℝ (sin x / x)^2 dx = π`.

The proof goes through the Fourier inversion formula applied to the triangle function
`tri ξ = max (1 - |ξ|) 0`, whose Fourier transform is `x ↦ sinc (π x)^2`.
-/

open MeasureTheory Real intervalIntegral
open scoped FourierTransform RealInnerProductSpace

namespace Zeta23Scaffold

/-- The triangle function `ξ ↦ max (1 - |ξ|) 0`, viewed as a complex-valued function. -/

lemma integral_exp_mul_tri (a : ℂ) : (∫ v : ℝ, Complex.exp (a * v) * tri v) =
    (∫ ξ in (-1:ℝ)..0, (1 + (ξ:ℂ)) * Complex.exp (a * ξ)) +
    (∫ ξ in (0:ℝ)..1, (1 - (ξ:ℂ)) * Complex.exp (a * ξ)) := by
  have hzero : ∀ v : ℝ, v ∉ Set.Ioc (-1:ℝ) 1 → Complex.exp (a * v) * tri v = 0 := by
    intro v hv
    simp only [Set.mem_Ioc, not_and_or, not_lt, not_le] at hv
    have : (1:ℝ) ≤ |v| := by
      rcases hv with h | h
      · rw [abs_of_nonpos (by linarith)]; linarith
      · rw [abs_of_nonneg (by linarith)]; linarith
    rw [tri_support this, mul_zero]
  rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hzero,
    ← intervalIntegral.integral_of_le (by norm_num : (-1:ℝ) ≤ 1),
    ← intervalIntegral.integral_add_adjacent_intervals
      (a := (-1:ℝ)) (b := 0) (c := 1) ?_ ?_]
  · congr 1
    · apply intervalIntegral.integral_congr
      intro v hv
      rw [Set.uIcc_of_le (by norm_num : (-1:ℝ) ≤ 0)] at hv
      simp only [Set.mem_Icc] at hv
      have hv' : |v| = -v := abs_of_nonpos hv.2
      simp only [tri, hv']
      rw [max_eq_left (by linarith [hv.1])]
      push_cast
      ring
    · apply intervalIntegral.integral_congr
      intro v hv
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hv
      simp only [Set.mem_Icc] at hv
      have hv' : |v| = v := abs_of_nonneg hv.1
      simp only [tri, hv']
      rw [max_eq_left (by linarith [hv.2])]
      push_cast
      ring
  · apply Continuous.intervalIntegrable
    exact Continuous.mul (by fun_prop) tri_continuous
  · apply Continuous.intervalIntegrable
    exact Continuous.mul (by fun_prop) tri_continuous

