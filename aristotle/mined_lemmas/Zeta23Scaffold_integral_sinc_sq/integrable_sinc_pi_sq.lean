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

lemma integrable_sinc_pi_sq :
    Integrable (fun w : ℝ => (Real.sin (π * w) / (π * w)) ^ 2) := by
  have hmeas : Measurable (fun w : ℝ => (Real.sin (π * w) / (π * w)) ^ 2) :=
    ((Real.measurable_sin.comp (measurable_const_mul π)).div
      (measurable_const_mul π)).pow_const 2
  refine Integrable.mono (integrable_inv_one_add_sq.const_mul 2) hmeas.aestronglyMeasurable ?_
  filter_upwards with w
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * (1 + w ^ 2)⁻¹)]
  exact sinc_sq_le w

/-- `∫ (sin (π w) / (π w))² dw = 1`: Fourier inversion for the tent function at `0`. -/
