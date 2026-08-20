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

lemma intervalIntegrable_id_mul_w (a b : ℝ) :
    IntervalIntegrable (fun u => u * w u) volume a b :=
  (continuous_id.mul continuous_w).intervalIntegrable a b

