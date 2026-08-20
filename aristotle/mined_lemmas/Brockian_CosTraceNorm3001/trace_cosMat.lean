import Mathlib

/-!
# Trace-norm bounds for the cosine of a Hermitian matrix (`CosTraceNorm` family)

For a complex `n × n` matrix `B` the *trace norm* (Schatten 1-norm) is the sum of the singular
values of `B`, i.e. the sum of the square roots of the eigenvalues of the positive semidefinite
matrix `Bᴴ * B`.  This file introduces that notion (`Brockian.traceNorm`), identifies it with
`∑ i, |eigenvalue i|` for Hermitian matrices, and proves a family of bounds for the matrix
`cos A := cfc Real.cos A` obtained from a Hermitian matrix `A` by the continuous functional
calculus.
-/

open scoped BigOperators
open Matrix Polynomial

namespace Brockian

variable {n : ℕ}

/-- The trace norm (Schatten 1-norm) of a complex matrix: the sum of its singular values,
i.e. the sum of the square roots of the eigenvalues of `Bᴴ * B`. -/

theorem trace_cosMat {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) :
    (cosMat A).trace = ((∑ i, Real.cos (hA.eigenvalues i) : ℝ) : ℂ) := by
  rw [(isHermitian_cosMat hA).trace_eq_sum_eigenvalues]
  have h := sum_eigenvalues_cfc Real.cos id hA
  simp only [id_eq] at h
  have h2 := congrArg (fun r : ℝ => (r : ℂ)) h
  push_cast at h2 ⊢
  exact h2

/-- **Upper trace-norm bound**: `‖cos A‖₁ ≤ n`. -/
