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

theorem integrableOn_affine_mul_w (a c d : ℝ) :
    IntegrableOn (fun u => (c * u + d) * w u) (Ioi a) := by
  simpa using integrableOn_affine_mul_w_shift a c d 0

/-- `∫_0^∞ u * w u du = π²/3`. -/
