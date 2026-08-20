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

lemma tri_continuous : Continuous tri := by unfold tri; fun_prop

