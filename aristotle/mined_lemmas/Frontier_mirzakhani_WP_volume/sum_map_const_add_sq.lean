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

lemma sum_map_const_add_sq (c : ℝ) (s : Multiset ℝ) :
    (s.map fun L => c + L ^ 2).sum = (Multiset.card s : ℝ) * c + sqSum s := by
  induction s using Multiset.induction_on with
  | empty => simp [sqSum]
  | cons a s ih => simp [sqSum, ih] at *; ring

/-- A function carrying the known small Weil–Petersson volumes: the pair of pants, the
one-holed torus and the four-holed sphere. -/
