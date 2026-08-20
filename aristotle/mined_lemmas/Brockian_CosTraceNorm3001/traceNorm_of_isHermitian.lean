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

theorem traceNorm_of_isHermitian {B : Matrix (Fin n) (Fin n) ℂ} (hB : B.IsHermitian) :
    traceNorm B = ∑ i, |hB.eigenvalues i| := by
  have h := sum_eigenvalues_of_charpoly_eq (Matrix.isHermitian_conjTranspose_mul_self B)
    (fun i => (hB.eigenvalues i) ^ 2) (charpoly_conjTranspose_mul_self hB) Real.sqrt
  rw [traceNorm, h]
  exact Finset.sum_congr rfl fun i _ => Real.sqrt_sq_eq_abs _

/-- `cfc f A` is Hermitian whenever `A` is. -/
