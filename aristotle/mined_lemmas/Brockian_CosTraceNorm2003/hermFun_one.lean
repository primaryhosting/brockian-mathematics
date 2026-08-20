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

lemma hermFun_one {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    hermFun hA (fun _ => 1) = 1 := by
  rw [hermFun]
  simp only [Complex.ofReal_one, Matrix.diagonal_one]
  exact map_one (Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) hA.eigenvectorUnitary)

