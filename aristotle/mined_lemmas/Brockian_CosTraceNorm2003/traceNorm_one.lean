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

lemma traceNorm_one : traceNorm (1 : Matrix n n ℂ) = (Fintype.card n : ℝ) := by
  have hH : (1 : Matrix n n ℂ).IsHermitian := Matrix.isHermitian_one
  rw [traceNorm_of_isHermitian hH]
  have hchar : (1 : Matrix n n ℂ).charpoly = ∏ _i : n, (X - C (((1 : ℝ) : ℂ))) := by
    rw [← Matrix.diagonal_one, Matrix.charpoly_diagonal]
    simp
  rw [sum_eigenvalues_of_charpoly hH (fun _ => (1 : ℝ)) hchar (fun x => |x|)]
  simp

/-- Sanity check: the matrix cosine and sine satisfy the Pythagorean identity. -/
