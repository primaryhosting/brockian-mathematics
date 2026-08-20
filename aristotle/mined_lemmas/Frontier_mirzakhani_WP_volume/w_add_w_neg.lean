import Mathlib

/-!
# The Fermi–Dirac integral `∫_0^∞ t/(1+e^t) dt = π²/12`

This auxiliary file establishes the elementary integral underlying Mirzakhani's
integration kernel, via the Mellin transform of the Dirichlet eta function.
-/


open Real MeasureTheory Set Complex
open scoped Real

namespace Mirzakhani

/-- Coefficients of the Dirichlet eta series, with the (irrelevant) `n = 0` term set to `0`. -/

lemma w_add_w_neg (u : ℝ) : w u + w (-u) = 1 := by
  have h1 : (0:ℝ) < 1 + rexp (u / 2) := by positivity
  have h2 : (0:ℝ) < 1 + rexp (-u / 2) := by positivity
  have hne : rexp (-u/2) = (rexp (u/2))⁻¹ := by
    rw [show (-u/2) = -(u/2) by ring, Real.exp_neg]
  have hx : (0:ℝ) < rexp (u/2) := Real.exp_pos _
  simp only [w]
  rw [hne]
  field_simp
  ring

