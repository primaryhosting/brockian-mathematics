import Mathlib
/-!
# Integral Sinc Sq
Category: C Integral
Target: Zeta23Scaffold.integral_sinc_sq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Real Complex
open scoped FourierTransform

noncomputable section

namespace Zeta23Scaffold

/-- The tent function `t ↦ max (1 - |t|) 0`. -/

lemma continuous_tent : Continuous tent :=
  Complex.continuous_ofReal.comp continuous_tentR

