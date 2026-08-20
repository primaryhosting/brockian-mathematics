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

lemma tentC_eq_zero_of_notMem {t : ℝ} (ht : t ∉ Set.Icc (-1 : ℝ) 1) : tentC t = 0 := by
  simp [tentC, tent_eq_zero_of_notMem ht]

