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

lemma integral_tri_exp_left (c : ℂ) (hc : c ≠ 0) :
    (∫ v in (-1 : ℝ)..0, Complex.exp (c * v) * tri v)
      = 1 / c - 1 / c ^ 2 + Complex.exp (-c) / c ^ 2 := by
  have hcong : ∫ v in (-1 : ℝ)..0, Complex.exp (c * v) * tri v
      = ∫ v in (-1 : ℝ)..0, Complex.exp (c * v) * (1 + (v : ℂ)) := by
    refine intervalIntegral.integral_congr ?_
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 0)] at hx
    obtain ⟨h1, h2⟩ := hx
    have habs : |x| = -x := abs_of_nonpos h2
    simp only [tri, habs]
    rw [max_eq_left (by linarith)]
    push_cast; ring
  rw [hcong, intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hasDerivAt_primitive_left c hc x)
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  push_cast
  simp only [Complex.exp_zero, mul_zero]
  field_simp
  ring

