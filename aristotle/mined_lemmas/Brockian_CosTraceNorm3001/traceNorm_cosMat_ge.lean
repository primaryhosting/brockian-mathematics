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

theorem traceNorm_cosMat_ge {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) :
    (n : ℝ) - (∑ i, (hA.eigenvalues i) ^ 2) / 2 ≤ traceNorm (cosMat A) := by
  rw [traceNorm_cosMat hA]
  have h : ∀ i : Fin n, 1 - (hA.eigenvalues i) ^ 2 / 2 ≤ |Real.cos (hA.eigenvalues i)| :=
    fun i => le_trans (Real.one_sub_sq_div_two_le_cos) (le_abs_self _)
  calc (n : ℝ) - (∑ i, (hA.eigenvalues i) ^ 2) / 2
      = ∑ i, (1 - (hA.eigenvalues i) ^ 2 / 2) := by
        rw [Finset.sum_sub_distrib, ← Finset.sum_div]; simp
    _ ≤ ∑ i, |Real.cos (hA.eigenvalues i)| := Finset.sum_le_sum fun i _ => h i

/-- The trace of `cos A` is bounded in absolute value by its trace norm. -/
