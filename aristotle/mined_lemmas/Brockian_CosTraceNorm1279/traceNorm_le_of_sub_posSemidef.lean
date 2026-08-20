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

lemma traceNorm_le_of_sub_posSemidef {P N : Matrix ι ι ℝ} (hA : A.IsHermitian)
    (hP : P.PosSemidef) (hN : N.PosSemidef) (hPN : A = P - N) :
    traceNorm hA ≤ P.trace + N.trace := by
  subst hPN
  have hev : ∀ i, hA.eigenvalues i =
      (star (⇑(hA.eigenvectorBasis i) : ι → ℝ) ⬝ᵥ (P *ᵥ (⇑(hA.eigenvectorBasis i) : ι → ℝ)))
      - (star (⇑(hA.eigenvectorBasis i) : ι → ℝ) ⬝ᵥ
          (N *ᵥ (⇑(hA.eigenvectorBasis i) : ι → ℝ))) := by
    intro i
    rw [hA.eigenvalues_eq i]
    simp [Matrix.sub_mulVec, dotProduct_sub]
  calc traceNorm hA
      ≤ ∑ i, ((star (⇑(hA.eigenvectorBasis i) : ι → ℝ) ⬝ᵥ
            (P *ᵥ (⇑(hA.eigenvectorBasis i) : ι → ℝ)))
          + (star (⇑(hA.eigenvectorBasis i) : ι → ℝ) ⬝ᵥ
            (N *ᵥ (⇑(hA.eigenvectorBasis i) : ι → ℝ)))) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [hev i]
        exact abs_sub_le_iff.mpr
          ⟨by linarith [hN.dotProduct_mulVec_nonneg (⇑(hA.eigenvectorBasis i) : ι → ℝ)],
           by linarith [hP.dotProduct_mulVec_nonneg (⇑(hA.eigenvectorBasis i) : ι → ℝ)]⟩
    _ = P.trace + N.trace := by
        rw [Finset.sum_add_distrib, sum_eigenbasis_quadraticForm hA P,
          sum_eigenbasis_quadraticForm hA N]

end TraceNorm

section Cos

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The cosine Gram matrix of the phases `θ` at frequency `f`. -/
