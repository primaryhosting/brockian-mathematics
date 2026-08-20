import Mathlib

/-!
# Integral Sinc Sq
Category: C Integral
Target: Zeta23Scaffold.integral_sinc_sq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Complex Filter intervalIntegral
open scoped FourierTransform Topology Real

namespace Zeta23Scaffold

/-- The triangle ("tent") function `x ↦ max 0 (1 - |x|)`, viewed as a complex-valued function. -/

lemma tri_eq_zero {x : ℝ} (hx : 1 ≤ |x|) : tri x = 0 := by
  simp only [tri, Complex.ofReal_eq_zero]
  exact max_eq_left (by linarith)

