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

theorem CosTraceNorm2003_one_sub_cos {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    traceNorm (1 - cosMat hA) ≤ (1 / 2) * traceNorm (A * A) := by
  have h1 : (1 : Matrix n n ℂ) - cosMat hA = hermFun hA (fun x => 1 - Real.cos x) := by
    rw [cosMat, ← hermFun_one hA, hermFun_sub]
  rw [h1, traceNorm_hermFun, traceNorm_sq_of_isHermitian hA, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have hc := Real.one_sub_sq_div_two_le_cos (x := hA.eigenvalues i)
  have hle : 1 - Real.cos (hA.eigenvalues i) ≤ 1 / 2 * (hA.eigenvalues i) ^ 2 := by linarith
  have hnn : 0 ≤ 1 - Real.cos (hA.eigenvalues i) := by
    have := Real.cos_le_one (hA.eigenvalues i); linarith
  rwa [abs_of_nonneg hnn]

/-- Scalar ingredient: `1 ≤ |cos x| + |sin x|`. -/
