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

lemma integral_tri_exp_split (c : ℂ) :
    ∫ v : ℝ, Complex.exp (c * v) * tri v
      = (∫ v in (-1 : ℝ)..0, Complex.exp (c * v) * tri v)
        + ∫ v in (0 : ℝ)..1, Complex.exp (c * v) * tri v := by
  have h0 : ∫ v : ℝ, Complex.exp (c * v) * tri v
      = ∫ v in Set.Ioc (-1 : ℝ) 1, Complex.exp (c * v) * tri v := by
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero ?_).symm
    intro x hx
    simp only [Set.mem_Ioc, not_and_or, not_lt, not_le] at hx
    have : tri x = 0 := by
      refine tri_eq_zero_of_one_le_abs ?_
      rcases hx with h | h
      · exact le_abs.2 (Or.inr (by linarith))
      · exact le_abs.2 (Or.inl (by linarith))
    simp [this]
  rw [h0, ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
    ← intervalIntegral.integral_add_adjacent_intervals (b := 0)
      (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _)]

/-- The total integral `∫ exp (c x) * tri x` in closed form, for `c ≠ 0`. -/
