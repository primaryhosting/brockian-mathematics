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

lemma integral_tentC_sq : ∫ t : ℝ, tentC t * tentC t = (2 / 3 : ℂ) := by
  have hfun : ∀ t : ℝ, tentC t * tentC t = (((max 0 (1 - |t|) : ℝ) ^ 2 : ℝ) : ℂ) := by
    intro t
    simp only [tentC, ← Complex.ofReal_mul]
    norm_cast
    ring
  simp_rw [hfun]
  rw [integral_complex_ofReal, integral_tent_sq]
  norm_num

