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

theorem cosMatrix_bilinForm_bound (x : Fin n → ℝ) (u v : Fin n → ℝ) :
    |u ⬝ᵥ (cosMatrix x).mulVec v| ≤
      traceNorm (cosMatrix x) (cosMatrix_isHermitian x) *
        (Real.sqrt (∑ i, u i ^ 2) * Real.sqrt (∑ i, v i ^ 2)) := by
  set U := Real.sqrt (∑ i, u i ^ 2) with hU
  set V := Real.sqrt (∑ i, v i ^ 2) with hV
  rw [CosTraceNorm2707]
  -- Cauchy–Schwarz for the positive semidefinite form, plus `vᵀ C v ≤ n ‖v‖²`.
  have hCS : |u ⬝ᵥ (cosMatrix x).mulVec v| ≤
      Real.sqrt (u ⬝ᵥ (cosMatrix x).mulVec u) * Real.sqrt (v ⬝ᵥ (cosMatrix x).mulVec v) := by
    rw [cosMatrix_bilinForm, cosMatrix_quadForm, cosMatrix_quadForm]
    set a1 := ∑ i, u i * Real.cos (x i)
    set a2 := ∑ i, u i * Real.sin (x i)
    set b1 := ∑ i, v i * Real.cos (x i)
    set b2 := ∑ i, v i * Real.sin (x i)
    rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_sq_eq_abs]
    apply Real.sqrt_le_sqrt
    nlinarith [sq_nonneg (a1 * b2 - a2 * b1)]
  have hbu : u ⬝ᵥ (cosMatrix x).mulVec u ≤ n * ∑ i, u i ^ 2 := by
    have := (cosMatrix_quadForm_bounds x u).2
    rwa [CosTraceNorm2707] at this
  have hbv : v ⬝ᵥ (cosMatrix x).mulVec v ≤ n * ∑ i, v i ^ 2 := by
    have := (cosMatrix_quadForm_bounds x v).2
    rwa [CosTraceNorm2707] at this
  have hsu : Real.sqrt (u ⬝ᵥ (cosMatrix x).mulVec u) ≤ Real.sqrt (n : ℝ) * U := by
    rw [hU, ← Real.sqrt_mul (by positivity)]
    exact Real.sqrt_le_sqrt hbu
  have hsv : Real.sqrt (v ⬝ᵥ (cosMatrix x).mulVec v) ≤ Real.sqrt (n : ℝ) * V := by
    rw [hV, ← Real.sqrt_mul (by positivity)]
    exact Real.sqrt_le_sqrt hbv
  have hsq : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) :=
    Real.mul_self_sqrt (by positivity)
  calc |u ⬝ᵥ (cosMatrix x).mulVec v|
      ≤ Real.sqrt (u ⬝ᵥ (cosMatrix x).mulVec u) * Real.sqrt (v ⬝ᵥ (cosMatrix x).mulVec v) := hCS
    _ ≤ (Real.sqrt (n : ℝ) * U) * (Real.sqrt (n : ℝ) * V) :=
        mul_le_mul hsu hsv (Real.sqrt_nonneg _) (by positivity)
    _ = (n : ℝ) * (U * V) := by rw [mul_mul_mul_comm, hsq]



section Weighted

/-- The weighted cosine Gram matrix `C i j = a i * a j * cos (x i - x j)`. -/
