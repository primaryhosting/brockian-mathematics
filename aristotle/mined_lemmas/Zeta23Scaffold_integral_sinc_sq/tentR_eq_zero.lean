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

lemma tentR_eq_zero {t : ℝ} (h : 1 ≤ |t|) : tentR t = 0 := by
  simp only [tentR, max_eq_right_iff]
  linarith

