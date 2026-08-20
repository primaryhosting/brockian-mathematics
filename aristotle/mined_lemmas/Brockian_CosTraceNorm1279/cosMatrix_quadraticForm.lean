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

lemma cosMatrix_quadraticForm (f : ℝ) (θ : ι → ℝ) (x : ι → ℝ) :
    star x ⬝ᵥ (cosMatrix f θ *ᵥ x)
      = (∑ i, x i * Real.cos (f * θ i)) ^ 2 + (∑ i, x i * Real.sin (f * θ i)) ^ 2 := by
  simp only [dotProduct, mulVec, cosMatrix, Matrix.of_apply, star_trivial, sq,
    Finset.sum_mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_sub, Real.cos_sub]
  ring

omit [DecidableEq ι] in
