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

lemma traceNorm_sq_of_isHermitian {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    traceNorm (A * A) = ∑ i, (hA.eigenvalues i) ^ 2 := by
  have h : A * A = hermFun hA (fun x => x * x) := by
    rw [← hermFun_mul, hermFun_id]
  rw [h, traceNorm_hermFun]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [abs_of_nonneg (mul_self_nonneg _), sq]

