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

