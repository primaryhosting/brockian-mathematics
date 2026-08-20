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

theorem traceNorm_cosMat_le {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) :
    traceNorm (cosMat A) ≤ (n : ℝ) := by
  rw [traceNorm_cosMat hA]
  calc ∑ i, |Real.cos (hA.eigenvalues i)| ≤ ∑ _i : Fin n, (1 : ℝ) :=
        Finset.sum_le_sum fun i _ => Real.abs_cos_le_one _
    _ = (n : ℝ) := by simp

/-- **Lower trace-norm bound**: `‖cos A‖₁ ≥ n - (∑ λᵢ²)/2`. -/
