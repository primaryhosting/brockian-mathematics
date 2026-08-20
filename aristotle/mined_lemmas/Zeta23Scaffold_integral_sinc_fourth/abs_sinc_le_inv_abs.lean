import Mathlib

/-!
# Integral Sinc Fourth
Category: C Integral
Target: Zeta23Scaffold.integral_sinc_fourth
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Real Complex
open scoped FourierTransform

namespace Zeta23Scaffold

/-- Explicit antiderivative computation: the interval integral of a linear function times a
complex exponential. -/

lemma abs_sinc_le_inv_abs {x : ℝ} (hx : x ≠ 0) : |Real.sinc x| ≤ |x|⁻¹ := by
  rw [Real.sinc_of_ne_zero hx, abs_div]
  rw [div_le_iff₀ (abs_pos.2 hx), inv_mul_cancel₀ (abs_pos.2 hx).ne']
  exact Real.abs_sin_le_one x

