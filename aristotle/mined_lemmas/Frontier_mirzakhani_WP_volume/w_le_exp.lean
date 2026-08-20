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

lemma w_le_exp (u : ℝ) : w u ≤ rexp (-(u / 2)) := by
  have hx : (0:ℝ) < rexp (u / 2) := Real.exp_pos _
  have h1 : (0:ℝ) < 1 + rexp (u / 2) := by positivity
  rw [Real.exp_neg]
  rw [w, div_le_iff₀ h1]
  rw [inv_mul_eq_div, le_div_iff₀ hx]
  nlinarith

