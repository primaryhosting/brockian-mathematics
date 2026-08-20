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

noncomputable def fermiDirac : ℝ → ℂ := fun t => ((1 / (1 + rexp t) : ℝ) : ℂ)

/-- `∑_{n≥1} (-1)^{n+1}/n² = π²/12`. -/
