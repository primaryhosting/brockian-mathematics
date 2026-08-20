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

theorem traceNorm_sinMat {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) :
    traceNorm (sinMat A) = ∑ i, |Real.sin (hA.eigenvalues i)| := by
  rw [traceNorm_of_isHermitian (isHermitian_sinMat hA)]
  exact sum_eigenvalues_cfc Real.sin abs hA

/-- The trace of `cos A` is the sum of `cos λᵢ` over the eigenvalues `λᵢ` of `A`. -/
