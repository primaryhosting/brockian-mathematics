import Mathlib

/-!
# `Brockian.CosTraceNorm2707` : trace-norm bounds for cosine Gram matrices

For a family of angles `x : Fin n → ℝ` we consider the *cosine matrix*
`C i j = cos (x i - x j)`.  It is the Gram matrix of the unit vectors
`(cos (x i), sin (x i))` in the plane, hence positive semidefinite of rank at most `2`,
and all its diagonal entries equal `1`.

The main results are:

* `Brockian.cosMatrix_posSemidef` : `C` is positive semidefinite;
* `Brockian.traceNorm_of_posSemidef` : for a positive semidefinite matrix the trace norm
  (the sum of the absolute values of the eigenvalues) equals the trace;
* `Brockian.CosTraceNorm2707` : the trace norm of `C` equals `n`;
* derived trace-norm bounds: bounds on the quadratic and bilinear forms of `C`,
  and the general inequality `|trace A| ≤ ‖A‖₁` for Hermitian `A`.
-/

open scoped BigOperators

namespace Brockian

variable {n : ℕ}

/-- The cosine Gram matrix of a family of angles: `C i j = cos (x i - x j)`. -/

theorem cosMatrix_quadForm_bounds (x : Fin n → ℝ) (v : Fin n → ℝ) :
    0 ≤ v ⬝ᵥ (cosMatrix x).mulVec v ∧
      v ⬝ᵥ (cosMatrix x).mulVec v ≤
        traceNorm (cosMatrix x) (cosMatrix_isHermitian x) * ∑ i, v i ^ 2 := by
  have hq := cosMatrix_quadForm x v
  refine ⟨by rw [hq]; positivity, ?_⟩
  rw [CosTraceNorm2707, hq]
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ v (fun i => Real.cos (x i))
  have hs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ v (fun i => Real.sin (x i))
  have hsum : ((∑ i, Real.cos (x i) ^ 2) + ∑ i, Real.sin (x i) ^ 2) = n := by
    rw [← Finset.sum_add_distrib]
    simp [Real.cos_sq_add_sin_sq]
  nlinarith [Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => sq_nonneg (v i))]

/-- All entries of the cosine matrix are bounded by `1`. -/
