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
noncomputable def cosMatrix (x : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => Real.cos (x i - x j)

@[simp] lemma cosMatrix_apply (x : Fin n → ℝ) (i j : Fin n) :
    cosMatrix x i j = Real.cos (x i - x j) := rfl

/-- The cosine matrix is symmetric, hence Hermitian over `ℝ`. -/
lemma cosMatrix_isHermitian (x : Fin n → ℝ) : (cosMatrix x).IsHermitian := by
  ext i j
  simp [Matrix.conjTranspose_apply, ← Real.cos_neg (x j - x i)]

/-- The bilinear form of the cosine matrix splits into a cosine and a sine part. -/
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
lemma cosMatrix_quadForm (x : Fin n → ℝ) (v : Fin n → ℝ) :
    v ⬝ᵥ (cosMatrix x).mulVec v =
      (∑ i, v i * Real.cos (x i)) ^ 2 + (∑ i, v i * Real.sin (x i)) ^ 2 := by
  rw [cosMatrix_bilinForm, sq, sq]

/-- The cosine matrix is positive semidefinite. -/
lemma cosMatrix_posSemidef (x : Fin n → ℝ) : (cosMatrix x).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (cosMatrix_isHermitian x) fun v => ?_
  have hs : (star v : Fin n → ℝ) = v := by ext i; simp
  rw [hs, cosMatrix_quadForm]
  positivity

/-- The trace of the cosine matrix is `n`. -/
@[simp] lemma cosMatrix_trace (x : Fin n → ℝ) : (cosMatrix x).trace = n := by
  simp [Matrix.trace, Matrix.diag]

/-- The trace norm (nuclear / Schatten-1 norm) of a Hermitian real matrix:
the sum of the absolute values of its eigenvalues. -/
noncomputable def traceNorm (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) : ℝ :=
  ∑ i, |hA.eigenvalues i|

lemma traceNorm_nonneg (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) :
    0 ≤ traceNorm A hA :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- For a positive semidefinite matrix the trace norm coincides with the trace. -/
lemma traceNorm_of_posSemidef (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosSemidef) :
    traceNorm A hA.isHermitian = A.trace := by
  rw [traceNorm, Matrix.IsHermitian.trace_eq_sum_eigenvalues hA.isHermitian]
  exact Finset.sum_congr rfl fun i _ => abs_of_nonneg (hA.eigenvalues_nonneg i)

/-- The absolute value of the trace is at most the trace norm. -/
lemma abs_trace_le_traceNorm (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) :
    |A.trace| ≤ traceNorm A hA := by
  rw [Matrix.IsHermitian.trace_eq_sum_eigenvalues hA]
  exact Finset.abs_sum_le_sum_abs _ _

/-- **Main result.**  The trace norm of the cosine Gram matrix `C i j = cos (x i - x j)`
of any family of `n` angles equals `n`. -/
theorem CosTraceNorm2707 (x : Fin n → ℝ) :
    traceNorm (cosMatrix x) (cosMatrix_isHermitian x) = n := by
  rw [traceNorm_of_posSemidef (cosMatrix x) (cosMatrix_posSemidef x), cosMatrix_trace]

/-- Trace-norm (operator-type) bound for the quadratic form of the cosine matrix:
`0 ≤ vᵀ C v ≤ ‖C‖₁ * ‖v‖²`, with `‖C‖₁ = n`. -/
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
theorem cosMatrix_entry_abs_le_one (x : Fin n → ℝ) (i j : Fin n) :
    |cosMatrix x i j| ≤ 1 :=
  Real.abs_cos_le_one _

/-- Trace-norm bound for the bilinear form: `|uᵀ C v| ≤ ‖C‖₁ * ‖u‖ * ‖v‖` with `‖C‖₁ = n`. -/
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
noncomputable def weightedCosMatrix (a x : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => a i * a j * Real.cos (x i - x j)

@[simp] lemma weightedCosMatrix_apply (a x : Fin n → ℝ) (i j : Fin n) :
    weightedCosMatrix a x i j = a i * a j * Real.cos (x i - x j) := rfl

lemma weightedCosMatrix_isHermitian (a x : Fin n → ℝ) :
    (weightedCosMatrix a x).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, weightedCosMatrix_apply, star_trivial]
  rw [← Real.cos_neg (x j - x i), neg_sub]
  ring

/-- The quadratic form of the weighted cosine matrix is again a sum of two squares. -/
lemma weightedCosMatrix_quadForm (a x : Fin n → ℝ) (v : Fin n → ℝ) :
    v ⬝ᵥ (weightedCosMatrix a x).mulVec v =
      (∑ i, (v i * a i) * Real.cos (x i)) ^ 2 + (∑ i, (v i * a i) * Real.sin (x i)) ^ 2 := by
  rw [← cosMatrix_quadForm x fun i => v i * a i]
  simp only [dotProduct, Matrix.mulVec, weightedCosMatrix_apply, cosMatrix_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

lemma weightedCosMatrix_posSemidef (a x : Fin n → ℝ) : (weightedCosMatrix a x).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (weightedCosMatrix_isHermitian a x)
    fun v => ?_
  have hs : (star v : Fin n → ℝ) = v := by ext i; simp
  rw [hs, weightedCosMatrix_quadForm]
  positivity

@[simp] lemma weightedCosMatrix_trace (a x : Fin n → ℝ) :
    (weightedCosMatrix a x).trace = ∑ i, a i ^ 2 := by
  simp [Matrix.trace, Matrix.diag, sq]

/-- Trace norm of the weighted cosine Gram matrix `a i * a j * cos (x i - x j)`:
it equals `∑ i, a i ^ 2`.  Taking `a = 1` recovers `Brockian.CosTraceNorm2707`. -/
theorem weightedCosTraceNorm2707 (a x : Fin n → ℝ) :
    traceNorm (weightedCosMatrix a x) (weightedCosMatrix_isHermitian a x) = ∑ i, a i ^ 2 := by
  rw [traceNorm_of_posSemidef _ (weightedCosMatrix_posSemidef a x), weightedCosMatrix_trace]

end Weighted

end Brockian

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

