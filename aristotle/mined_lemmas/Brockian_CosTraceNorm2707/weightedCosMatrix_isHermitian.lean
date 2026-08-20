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

lemma weightedCosMatrix_isHermitian (a x : Fin n → ℝ) :
    (weightedCosMatrix a x).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, weightedCosMatrix_apply, star_trivial]
  rw [← Real.cos_neg (x j - x i), neg_sub]
  ring

/-- The quadratic form of the weighted cosine matrix is again a sum of two squares. -/
