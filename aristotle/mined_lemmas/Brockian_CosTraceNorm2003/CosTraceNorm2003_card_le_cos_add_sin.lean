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

theorem CosTraceNorm2003_card_le_cos_add_sin {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    (Fintype.card n : ℝ) ≤ traceNorm (cosMat hA) + traceNorm (sinMat hA) := by
  rw [cosMat, sinMat, traceNorm_hermFun, traceNorm_hermFun, ← Finset.sum_add_distrib]
  calc (Fintype.card n : ℝ) = ∑ _i : n, (1 : ℝ) := by simp
    _ ≤ ∑ i, (|Real.cos (hA.eigenvalues i)| + |Real.sin (hA.eigenvalues i)|) :=
        Finset.sum_le_sum fun i _ => one_le_abs_cos_add_abs_sin _

/-- **New trace-norm bounds for the matrix cosine and sine.**
For a Hermitian complex matrix `A`, with `‖·‖₁` the trace norm (Schatten 1-norm):
* `‖cos A‖₁ ≤ n`;
* `‖sin A‖₁ ≤ ‖A‖₁`;
* `‖1 - cos A‖₁ ≤ ½ ‖A‖₂²`, where `‖A‖₂² = ‖A * A‖₁` is the squared Frobenius norm;
* `n ≤ ‖cos A‖₁ + ‖sin A‖₁`. -/
