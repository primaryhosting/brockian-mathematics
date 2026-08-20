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

theorem CosTraceNorm2003_cos_le_card {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    traceNorm (cosMat hA) ≤ (Fintype.card n : ℝ) := by
  rw [cosMat, traceNorm_hermFun]
  calc ∑ i, |Real.cos (hA.eigenvalues i)| ≤ ∑ _i : n, (1 : ℝ) :=
        Finset.sum_le_sum fun _ _ => Real.abs_cos_le_one _
    _ = (Fintype.card n : ℝ) := by simp

/-- `‖sin A‖₁ ≤ ‖A‖₁` for a Hermitian matrix `A`. -/
