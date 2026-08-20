import Mathlib

/-!
# Trace-norm bounds for cosine Gram matrices (the `CosTraceNorm` family)

For a real symmetric matrix `A` we define its *trace norm* (nuclear norm, Schatten
`1`-norm) as the sum of the absolute values of its eigenvalues.

The main objects of study are the *cosine Gram matrices*
`cosMatrix f θ = (cos (f * (θ i - θ j)))_{i,j}` and their linear combinations
`cosCombo c f θ = ∑ k, c k • cosMatrix (f k) θ`.

The main result `Brockian.CosTraceNorm1279` gives two-sided trace-norm bounds for
`cosCombo c f θ` with arbitrary (possibly signed) coefficients `c`.
-/

namespace Brockian

open Matrix Finset

section TraceNorm

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℝ}

/-- The trace norm (nuclear norm, Schatten `1`-norm) of a real symmetric matrix:
the sum of the absolute values of its eigenvalues. -/

lemma sum_eigenbasis_quadraticForm (hA : A.IsHermitian) (P : Matrix ι ι ℝ) :
    ∑ i, (star (⇑(hA.eigenvectorBasis i) : ι → ℝ) ⬝ᵥ
      (P *ᵥ (⇑(hA.eigenvectorBasis i) : ι → ℝ))) = P.trace := by
  set U : Matrix ι ι ℝ := (hA.eigenvectorUnitary : Matrix ι ι ℝ) with hU
  have key : ∀ i, (star (⇑(hA.eigenvectorBasis i) : ι → ℝ) ⬝ᵥ
      (P *ᵥ (⇑(hA.eigenvectorBasis i) : ι → ℝ))) = (star U * P * U) i i := by
    intro i
    simp only [Matrix.mul_apply, dotProduct, mulVec, Matrix.star_apply, hU, Finset.mul_sum,
      Finset.sum_mul, mul_assoc, Matrix.IsHermitian.eigenvectorUnitary_apply, star_trivial]
    rw [Finset.sum_comm]
  simp_rw [key]
  have h1 : ∑ i, (star U * P * U) i i = (star U * P * U).trace := rfl
  have h2 : U * star U = 1 := by simp [hU]
  rw [h1, Matrix.trace_mul_cycle, h2, Matrix.one_mul]

/-- If a symmetric matrix is a difference of two positive semidefinite matrices, then its
trace norm is bounded by the sum of their traces. -/
