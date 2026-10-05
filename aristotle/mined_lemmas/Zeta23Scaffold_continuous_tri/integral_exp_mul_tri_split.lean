import Mathlib

/-!
# Integral Sinc Sq
Category: C Integral
Target: Zeta23Scaffold.integral_sinc_sq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Classical
open scoped FourierTransform

open MeasureTheory Complex

set_option maxHeartbeats 1000000

namespace Zeta23Scaffold

/-! ## The tent function and its Fourier transform

The proof of `∫ (sin x / x) ^ 2 dx = π` goes through Fourier inversion applied to the
tent (triangle) function `x ↦ max 0 (1 - |x|)`, whose Fourier transform is
`w ↦ (sin (π w) / (π w)) ^ 2`. -/

/-- The triangle (tent) function `x ↦ max 0 (1 - |x|)`, viewed as a complex-valued function. -/

lemma integral_exp_mul_tri_split (z : ℂ) :
    (∫ x : ℝ, Complex.exp (z * x) * tri x)
      = (∫ x in (-1:ℝ)..0, Complex.exp (z * x) * (1 + x))
        + (∫ x in (0:ℝ)..1, Complex.exp (z * x) * (1 - x)) := by
  have hcont : Continuous (fun x : ℝ => Complex.exp (z * x) * tri x) :=
    (by fun_prop : Continuous fun x : ℝ => Complex.exp (z * x)).mul continuous_tri
  have hsupp : ∀ x ∉ Set.Ioc (-1:ℝ) 1, Complex.exp (z * x) * tri x = 0 := by
    intro x hx
    simp only [Set.mem_Ioc, not_and_or, not_lt, not_le] at hx
    have h : 1 ≤ |x| := by
      rcases hx with h | h
      · rw [abs_of_nonpos (by linarith)]; linarith
      · rw [abs_of_nonneg (by linarith)]; linarith
    rw [tri_eq_zero_of_one_le_abs h, mul_zero]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hsupp,
    ← intervalIntegral.integral_of_le (by norm_num : (-1:ℝ) ≤ 1),
    ← intervalIntegral.integral_add_adjacent_intervals
      (b := (0:ℝ)) (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)]
  congr 1
  · apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (-1:ℝ) ≤ 0)] at hx
    simp only [Set.mem_Icc] at hx
    have h1 : |x| = -x := abs_of_nonpos hx.2
    have h4 : (max 0 (1 - |x|) : ℝ) = 1 + x := by
      rw [h1, max_eq_right (by linarith [hx.1] : (0:ℝ) ≤ 1 - -x)]; ring
    simp only [tri, h4]
    push_cast
    ring
  · apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hx
    simp only [Set.mem_Icc] at hx
    have h1 : |x| = x := abs_of_nonneg hx.1
    have h4 : (max 0 (1 - |x|) : ℝ) = 1 - x := by
      rw [h1, max_eq_right (by linarith [hx.2] : (0:ℝ) ≤ 1 - x)]
    simp only [tri, h4]
    push_cast
    ring

