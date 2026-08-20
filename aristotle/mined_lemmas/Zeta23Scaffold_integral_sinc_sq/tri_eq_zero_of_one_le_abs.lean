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

lemma tri_eq_zero_of_one_le_abs {x : ℝ} (hx : 1 ≤ |x|) : tri x = 0 := by
  simp only [tri, Complex.ofReal_eq_zero]
  exact max_eq_right (by linarith)

