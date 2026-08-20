import Mathlib

/-!
# Trace-norm bounds for the matrix cosine and sine (`CosTraceNorm` family)

This file develops, from scratch, the Schatten 1-norm (trace norm) of a complex square matrix,
the Hermitian functional calculus `Brockian.hermFun`, and proves a family of trace-norm bounds
for the matrix cosine and sine of a Hermitian matrix.
-/

set_option maxRecDepth 8000

open scoped BigOperators
open Matrix Polynomial

namespace Brockian

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The trace norm (Schatten 1-norm) of a complex square matrix: the sum of its singular
values, i.e. the sum of the square roots of the eigenvalues of `Aᴴ * A`. -/

lemma one_le_abs_cos_add_abs_sin (x : ℝ) : 1 ≤ |Real.cos x| + |Real.sin x| := by
  have hc : Real.cos x ^ 2 ≤ |Real.cos x| := by
    nlinarith [abs_nonneg (Real.cos x), Real.abs_cos_le_one x, sq_abs (Real.cos x)]
  have hs : Real.sin x ^ 2 ≤ |Real.sin x| := by
    nlinarith [abs_nonneg (Real.sin x), Real.abs_sin_le_one x, sq_abs (Real.sin x)]
  have := Real.sin_sq_add_cos_sq x
  linarith

/-- Trace-norm lower bound: `n ≤ ‖cos A‖₁ + ‖sin A‖₁` for a Hermitian `n × n` matrix `A`. -/
