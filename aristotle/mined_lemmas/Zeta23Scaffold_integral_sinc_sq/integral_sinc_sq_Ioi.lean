/-
# Integral Sinc Sq
Category: C Integral
Target: Zeta23Scaffold.integral_sinc_sq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above uses `/-` rather than `/-!` only because Lean 4 requires `import`
-- commands to precede every module docstring; the text is otherwise verbatim.)

import Mathlib

open Real Filter MeasureTheory Set

namespace Zeta23Scaffold

/-- For `x > 0`, the function `t ↦ t * exp (-(t * x))` is integrable on `(0, ∞)` and its
integral there equals `1 / x ^ 2`. -/

lemma integral_sinc_sq_Ioi : ∫ x in Ioi (0:ℝ), (Real.sin x / x) ^ 2 = π / 2 := by
  have hmeas : AEStronglyMeasurable (fun x : ℝ => (Real.sin x / x) ^ 2)
      (volume.restrict (Ioi 0)) := by
    apply Measurable.aestronglyMeasurable
    fun_prop
  have hnn : (0 : ℝ → ℝ) ≤ᵐ[volume.restrict (Ioi 0)] fun x : ℝ => (Real.sin x / x) ^ 2 := by
    filter_upwards with y using by positivity
  rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae hnn hmeas]
  have hrw : (fun x : ℝ => ENNReal.ofReal ((Real.sin x / x) ^ 2))
      = fun x : ℝ => ENNReal.ofReal (Real.sin x ^ 2 / x ^ 2) := by
    funext x; rw [div_pow]
  rw [hrw, lintegral_sin_sq_div_sq, ENNReal.toReal_ofReal (by positivity)]

/-- **The normalization integral of the sine kernel**:
`∫_ℝ (sin x / x) ^ 2 dx = π`.

The integrand is understood as the Lebesgue-measurable function `x ↦ (sin x / x) ^ 2`, which
takes the value `0` at `x = 0` in Lean's convention; since `{0}` is a null set this agrees
almost everywhere with the continuous extension `x ↦ sinc x ^ 2` (see `integral_sinc_sq'`). -/
