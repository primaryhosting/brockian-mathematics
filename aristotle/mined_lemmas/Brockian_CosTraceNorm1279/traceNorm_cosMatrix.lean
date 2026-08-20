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

theorem traceNorm_cosMatrix (f : ℝ) (θ : ι → ℝ) :
    traceNorm (cosMatrix_isHermitian f θ) = (Fintype.card ι : ℝ) := by
  rw [← cosMatrix_trace f θ]
  exact traceNorm_eq_trace_of_posSemidef (cosMatrix_posSemidef f θ)

omit [Fintype ι] [DecidableEq ι] in
/-- The splitting of `cosCombo` into its positive and negative parts. -/
