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

lemma tri_integrable : Integrable tri :=
  tri_continuous.integrable_of_hasCompactSupport tri_hasCompactSupport

/-- An antiderivative of `t ↦ exp (c t) (1 + t)`. -/
