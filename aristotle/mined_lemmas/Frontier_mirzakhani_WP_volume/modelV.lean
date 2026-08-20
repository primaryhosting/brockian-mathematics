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

noncomputable def modelV (g : ℕ) (s : Multiset ℝ) : ℝ :=
  if g = 0 ∧ Multiset.card s = 3 then 1
  else if g = 0 ∧ Multiset.card s = 4 then 2 * π ^ 2 + sqSum s / 2
  else if g = 1 ∧ Multiset.card s = 1 then (sqSum s + 4 * π ^ 2) / 24
  else 0

