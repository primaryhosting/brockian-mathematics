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

lemma cosMatrix_bilinForm (x : Fin n → ℝ) (u v : Fin n → ℝ) :
    u ⬝ᵥ (cosMatrix x).mulVec v =
      (∑ i, u i * Real.cos (x i)) * (∑ i, v i * Real.cos (x i)) +
        (∑ i, u i * Real.sin (x i)) * (∑ i, v i * Real.sin (x i)) := by
  have h1 : u ⬝ᵥ (cosMatrix x).mulVec v =
      ∑ i, ∑ j, (u i * Real.cos (x i) * (v j * Real.cos (x j)) +
        u i * Real.sin (x i) * (v j * Real.sin (x j))) := by
    simp only [dotProduct, Matrix.mulVec, cosMatrix_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
      rw [Real.cos_sub]; ring
  rw [h1, Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_add_distrib

/-- The quadratic form of the cosine matrix is a sum of two squares. -/
