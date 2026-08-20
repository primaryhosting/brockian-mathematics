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

lemma continuous_sincSqC : Continuous sincSqC := by
  unfold sincSqC
  exact Complex.continuous_ofReal.comp (((Real.continuous_sinc.comp
    (continuous_const.mul continuous_id)).pow 2))

