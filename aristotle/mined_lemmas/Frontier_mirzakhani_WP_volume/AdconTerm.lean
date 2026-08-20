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

noncomputable def AdconTerm (V : ℕ → Multiset ℝ → ℝ) (g : ℕ) (rest : Multiset ℝ) (t : ℝ) : ℝ :=
  (1 / 2) * ∫ x in Ioi (0:ℝ), ∫ y in Ioi (0:ℝ),
    x * y * Mirzakhani.H (x + y) t * splitSum V g rest x y

/-- The `B` term of Mirzakhani's recursion: the contribution of the pairs of pants having the
distinguished boundary and one further boundary component of the surface as boundary circles. -/
