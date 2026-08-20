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

lemma integrable_sinSq_div_sq : Integrable (fun x : ℝ => (Real.sin x / x) ^ 2) :=
  integrable_sincSq.congr sinSq_div_sq_ae_eq_sincSq.symm

