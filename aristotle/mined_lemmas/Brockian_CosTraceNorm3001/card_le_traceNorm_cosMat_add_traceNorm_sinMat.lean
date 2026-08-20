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

theorem card_le_traceNorm_cosMat_add_traceNorm_sinMat {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian) : (n : ℝ) ≤ traceNorm (cosMat A) + traceNorm (sinMat A) := by
  rw [traceNorm_cosMat hA, traceNorm_sinMat hA, ← Finset.sum_add_distrib]
  have h : ∀ i : Fin n,
      (1 : ℝ) ≤ |Real.cos (hA.eigenvalues i)| + |Real.sin (hA.eigenvalues i)| := by
    intro i
    set x := hA.eigenvalues i
    have hc : Real.cos x ^ 2 ≤ |Real.cos x| := by
      rw [← sq_abs (Real.cos x)]
      exact pow_le_of_le_one (abs_nonneg _) (Real.abs_cos_le_one x) (by norm_num)
    have hs : Real.sin x ^ 2 ≤ |Real.sin x| := by
      rw [← sq_abs (Real.sin x)]
      exact pow_le_of_le_one (abs_nonneg _) (Real.abs_sin_le_one x) (by norm_num)
    have := Real.sin_sq_add_cos_sq x
    linarith
  calc (n : ℝ) = ∑ _i : Fin n, (1 : ℝ) := by simp
    _ ≤ _ := Finset.sum_le_sum fun i _ => h i

/-- **`CosTraceNorm3001`**: trace-norm bounds for the cosine of a Hermitian matrix.

For every Hermitian `n × n` complex matrix `A`, writing `cos A` for the matrix obtained from `A`
by the continuous functional calculus and `‖·‖₁` for the trace norm (sum of singular values):

* `‖cos A‖₁ ≤ n`;
* `n - (∑ λᵢ²)/2 ≤ ‖cos A‖₁`, where the `λᵢ` are the eigenvalues of `A`;
* `‖tr (cos A)‖ ≤ ‖cos A‖₁`;
* `n ≤ ‖cos A‖₁ + ‖sin A‖₁`. -/
