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

lemma tent_fourier_aux (a : ℝ) :
    ∫ v in (-1 : ℝ)..1, Complex.exp ((↑(a * v)) * I) * ((1 - |v| : ℝ) : ℂ)
      = ((2 * ∫ v in (0 : ℝ)..1, (1 - v) * Real.cos (a * v) : ℝ) : ℂ) := by
  set F : ℝ → ℂ := fun v => Complex.exp ((↑(a * v)) * I) * ((1 - |v| : ℝ) : ℂ) with hF
  have hcont : Continuous F := by rw [hF]; fun_prop
  have hcont' : Continuous fun v : ℝ => F (-v) := hcont.comp continuous_neg
  have hneg : (∫ x in (-1 : ℝ)..0, F x) = ∫ x in (0 : ℝ)..1, F (-x) := by
    rw [intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := 1) (f := F)]
    norm_num
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := (0 : ℝ))
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _), hneg,
    ← intervalIntegral.integral_add (hcont'.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)]
  rw [show ((2 * ∫ v in (0 : ℝ)..1, (1 - v) * Real.cos (a * v) : ℝ) : ℂ)
      = ∫ v in (0 : ℝ)..1, ((2 * ((1 - v) * Real.cos (a * v)) : ℝ) : ℂ) by
    rw [intervalIntegral.integral_ofReal, ← intervalIntegral.integral_const_mul]]
  apply intervalIntegral.integral_congr
  intro v hv
  rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hv
  simp only [hF, abs_of_nonneg hv.1, abs_neg, mul_neg]
  rw [Complex.exp_mul_I, Complex.exp_mul_I]
  push_cast
  rw [Complex.cos_neg, Complex.sin_neg]
  ring

