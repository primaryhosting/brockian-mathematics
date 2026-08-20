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

lemma tent_integrable : Integrable (fun x : ℝ => (tent x : ℂ)) := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact Complex.continuous_ofReal.comp tent_continuous
  · apply HasCompactSupport.intro (isCompact_Icc (a := (-1 : ℝ)) (b := 1))
    intro x hx
    simp only [Set.mem_Icc, not_and_or, not_le] at hx
    have : tent x = 0 := by
      refine tent_eq_zero ?_
      rcases hx with h | h
      · exact le_abs.2 (Or.inr (by linarith))
      · exact le_abs.2 (Or.inl (by linarith))
    simp [this]

/-- Antiderivative computation: the integral of `(A + B x) exp (c x)`. -/
