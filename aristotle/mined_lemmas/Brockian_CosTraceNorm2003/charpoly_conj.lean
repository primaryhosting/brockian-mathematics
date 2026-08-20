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

lemma charpoly_conj (U : Matrix.unitaryGroup n ℂ) (d : n → ℝ) :
    (Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) U
      (Matrix.diagonal fun i => ((d i : ℝ) : ℂ))).charpoly = ∏ i, (X - C ((d i : ℝ) : ℂ)) := by
  rw [Unitary.conjStarAlgAut_apply, Matrix.charpoly_mul_comm, ← mul_assoc,
    Unitary.coe_star_mul_self, one_mul, Matrix.charpoly_diagonal]

/-- The trace norm computed from a list of "signed singular values". -/
