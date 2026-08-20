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

lemma cosMat_sq_add_sinMat_sq {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    cosMat hA * cosMat hA + sinMat hA * sinMat hA = 1 := by
  rw [cosMat, sinMat, hermFun_mul, hermFun_mul, ← hermFun_one hA, hermFun, hermFun, hermFun,
    ← map_add]
  congr 1
  ext i j
  by_cases h : i = j
  · subst h
    have hpy := Real.sin_sq_add_cos_sq (hA.eigenvalues i)
    have : Real.cos (hA.eigenvalues i) * Real.cos (hA.eigenvalues i)
        + Real.sin (hA.eigenvalues i) * Real.sin (hA.eigenvalues i) = 1 := by nlinarith
    simp only [Matrix.add_apply, Matrix.diagonal_apply_eq]
    rw [← Complex.ofReal_add, this]
  · simp [h]

/-- `‖cos A‖₁ ≤ n` for a Hermitian `n × n` matrix `A`. -/
