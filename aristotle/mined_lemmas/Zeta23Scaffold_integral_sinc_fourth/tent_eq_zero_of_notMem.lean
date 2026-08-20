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

lemma tent_eq_zero_of_notMem {t : ℝ} (ht : t ∉ Set.Icc (-1 : ℝ) 1) : max 0 (1 - |t|) = 0 := by
  simp only [Set.mem_Icc, not_and_or, not_le] at ht
  rcases ht with h | h
  · have : 1 ≤ |t| := by rw [abs_of_nonpos (by linarith)]; linarith
    simp [sub_nonpos.2 this]
  · have : 1 ≤ |t| := le_trans (by linarith) (le_abs_self t)
    simp [sub_nonpos.2 this]

