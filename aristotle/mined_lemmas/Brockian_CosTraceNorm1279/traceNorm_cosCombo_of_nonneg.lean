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

theorem traceNorm_cosCombo_of_nonneg {m : ℕ} {c : Fin m → ℝ} (f : Fin m → ℝ) (θ : ι → ℝ)
    (hc : ∀ k, 0 ≤ c k) :
    traceNorm (cosCombo_isHermitian c f θ) = (Fintype.card ι : ℝ) * ∑ k, c k := by
  rw [← cosCombo_trace c f θ]
  exact traceNorm_eq_trace_of_posSemidef (cosCombo_posSemidef f θ hc)

/-- The trace norm of a single cosine Gram matrix is the cardinality of the index set. -/
