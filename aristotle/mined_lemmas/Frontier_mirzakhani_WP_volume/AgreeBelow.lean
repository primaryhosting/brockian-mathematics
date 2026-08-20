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

def AgreeBelow (V W : ℕ → Multiset ℝ → ℝ) (M : ℕ) : Prop :=
  ∀ (g' : ℕ) (s' : Multiset ℝ), 2 * g' + Multiset.card s' < M → 3 ≤ 2 * g' + Multiset.card s' →
    s' ≠ 0 → V g' s' = W g' s'

