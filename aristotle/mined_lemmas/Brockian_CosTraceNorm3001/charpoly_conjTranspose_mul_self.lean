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

theorem charpoly_conjTranspose_mul_self {B : Matrix (Fin n) (Fin n) ℂ} (hB : B.IsHermitian) :
    (Bᴴ * B).charpoly = ∏ i, (X - C (((hB.eigenvalues i) ^ 2 : ℝ) : ℂ)) := by
  have hsa : IsSelfAdjoint B := hB
  have h0 : cfc (fun x : ℝ => x ^ 2) B = B ^ 2 := cfc_pow_id (R := ℝ) B 2 hsa
  have h1 : Bᴴ * B = cfc (fun x : ℝ => x ^ 2) B := by rw [h0, hB.eq, sq]
  rw [h1, hB.charpoly_cfc_eq]
  simp

/-- The trace norm of a Hermitian matrix is the sum of the absolute values of its eigenvalues. -/
