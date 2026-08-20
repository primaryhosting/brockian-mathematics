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

theorem CosTraceNorm2003_sin_le_traceNorm {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    traceNorm (sinMat hA) ≤ traceNorm A := by
  rw [sinMat, traceNorm_hermFun, traceNorm_of_isHermitian hA]
  exact Finset.sum_le_sum fun _ _ => Real.abs_sin_le_abs

/-- `‖1 - cos A‖₁ ≤ ½ ‖A‖₂²` for a Hermitian matrix `A`. -/
