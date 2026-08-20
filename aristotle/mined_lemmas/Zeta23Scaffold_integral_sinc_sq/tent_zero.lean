/-
# Integral Sinc Sq
Category: C Integral
Target: Zeta23Scaffold.integral_sinc_sq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open MeasureTheory Real Complex
open scoped FourierTransform

namespace Zeta23Scaffold

/-! ### The tent function and its Fourier transform -/

/-- The triangular ("tent") function `max (1 - |x|) 0`, supported on `[-1, 1]`. -/

lemma tent_zero : tent 0 = 1 := by simp [tent]

