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

lemma hermFun_isHermitian {A : Matrix n n ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (hermFun hA f).IsHermitian := by
  have : star (hermFun hA f) = hermFun hA f := by
    rw [hermFun, ← map_star]
    congr 1
    rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
    simp
  simp [Matrix.star_eq_conjTranspose] at this
  exact this

