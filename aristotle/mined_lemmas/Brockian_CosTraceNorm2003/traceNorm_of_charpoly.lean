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

lemma traceNorm_of_charpoly {M : Matrix n n ℂ} (μ : n → ℝ)
    (h : (Mᴴ * M).charpoly = ∏ i, (X - C (((μ i) ^ 2 : ℝ) : ℂ))) :
    traceNorm M = ∑ i, |μ i| := by
  have := sum_eigenvalues_of_charpoly (Matrix.isHermitian_conjTranspose_mul_self M)
    (fun i => (μ i) ^ 2) h Real.sqrt
  rw [traceNorm, this]
  exact Finset.sum_congr rfl fun i _ => Real.sqrt_sq_eq_abs _

