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

lemma traceNorm_hermFun {A : Matrix n n ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    traceNorm (hermFun hA f) = ∑ i, |f (hA.eigenvalues i)| := by
  refine traceNorm_of_charpoly (fun i => f (hA.eigenvalues i)) ?_
  have hH : (hermFun hA f)ᴴ = hermFun hA f :=
    (hermFun_isHermitian hA f)
  rw [hH, hermFun_mul]
  have := charpoly_conj hA.eigenvectorUnitary (fun i => f (hA.eigenvalues i) * f (hA.eigenvalues i))
  rw [hermFun]
  simp only [sq]
  convert this using 3

/-- The trace norm of a Hermitian matrix is the sum of the absolute values of its
eigenvalues. -/
