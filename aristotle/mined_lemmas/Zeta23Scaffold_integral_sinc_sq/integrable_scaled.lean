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

lemma integrable_scaled : Integrable (fun ξ : ℝ => (Real.sin (π * ξ) / (π * ξ)) ^ 2) :=
  integrable_sinSq_div_sq.comp_mul_left' Real.pi_ne_zero

