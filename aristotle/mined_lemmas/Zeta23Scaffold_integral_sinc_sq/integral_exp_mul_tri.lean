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

