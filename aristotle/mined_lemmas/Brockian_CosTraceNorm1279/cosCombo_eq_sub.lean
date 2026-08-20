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

lemma cosCombo_eq_sub {m : ℕ} (c f : Fin m → ℝ) (θ : ι → ℝ) :
    cosCombo c f θ = cosCombo (fun k => max (c k) 0) f θ
      - cosCombo (fun k => max (-c k) 0) f θ := by
  simp only [cosCombo, ← Finset.sum_sub_distrib, ← sub_smul]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  rcases le_total 0 (c k) with h | h
  · rw [max_eq_left h, max_eq_right (by linarith), sub_zero]
  · rw [max_eq_right h, max_eq_left (by linarith), zero_sub, neg_neg]

/-- **Trace-norm bounds for cosine Gram combinations.**
For arbitrary real coefficients `c` and frequencies `f`, the trace norm of
`cosCombo c f θ = ∑ k, c k • (cos (f k * (θ i - θ j)))_{i,j}` satisfies
`|card ι * ∑ k, c k| ≤ ‖cosCombo c f θ‖₁ ≤ card ι * ∑ k, |c k|`.
The two bounds coincide (so both are attained) when all `c k` have the same sign. -/
