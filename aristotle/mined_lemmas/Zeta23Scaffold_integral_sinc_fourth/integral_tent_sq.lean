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

