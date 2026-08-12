import Mathlib

/-!
# Trace-norm bounds for the cosine of a Hermitian matrix (`CosTraceNorm` family)

For a complex `n × n` matrix `B` the *trace norm* (Schatten 1-norm) is the sum of the singular
values of `B`, i.e. the sum of the square roots of the eigenvalues of the positive semidefinite
matrix `Bᴴ * B`.  This file introduces that notion (`Brockian.traceNorm`), identifies it with
`∑ i, |eigenvalue i|` for Hermitian matrices, and proves a family of bounds for the matrix
`cos A := cfc Real.cos A` obtained from a Hermitian matrix `A` by the continuous functional
calculus.
-/

open scoped BigOperators
open Matrix Polynomial

namespace Brockian

variable {n : ℕ}

/-- The trace norm (Schatten 1-norm) of a complex matrix: the sum of its singular values,
i.e. the sum of the square roots of the eigenvalues of `Bᴴ * B`. -/
noncomputable def traceNorm (B : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  ∑ i, Real.sqrt ((Matrix.isHermitian_conjTranspose_mul_self B).eigenvalues i)

/-- The cosine of a Hermitian matrix, defined by the continuous functional calculus. -/
noncomputable def cosMat (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  cfc Real.cos A

/-- The sine of a Hermitian matrix, defined by the continuous functional calculus. -/
noncomputable def sinMat (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  cfc Real.sin A

/-- If the characteristic polynomial of a Hermitian matrix `B` factors with the real numbers
`d i` as roots, then any real function of the eigenvalues of `B` sums to the same value as the
corresponding function of the `d i`. -/
theorem sum_eigenvalues_of_charpoly_eq {B : Matrix (Fin n) (Fin n) ℂ} (hB : B.IsHermitian)
    (d : Fin n → ℝ) (hd : B.charpoly = ∏ i, (X - C ((d i : ℂ)))) (g : ℝ → ℝ) :
    ∑ i, g (hB.eigenvalues i) = ∑ i, g (d i) := by
  have h1 : B.charpoly.roots = Multiset.map (RCLike.ofReal ∘ hB.eigenvalues) Finset.univ.val :=
    hB.roots_charpoly_eq_eigenvalues
  have h2 : B.charpoly.roots = Multiset.map (fun i => ((d i : ℂ))) Finset.univ.val := by
    rw [hd, Polynomial.roots_prod]
    · simp
    · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]
  have h3 := h1.symm.trans h2
  have h4 := congrArg (Multiset.map (fun z : ℂ => g (RCLike.re z))) h3
  simp only [Multiset.map_map, Function.comp_def, RCLike.ofReal_re] at h4
  have h5 := congrArg Multiset.sum h4
  simpa [Finset.sum, Function.comp_def] using h5

/-- For a Hermitian matrix `B`, the matrix `Bᴴ * B` has characteristic polynomial with roots the
squares of the eigenvalues of `B`. -/
theorem charpoly_conjTranspose_mul_self {B : Matrix (Fin n) (Fin n) ℂ} (hB : B.IsHermitian) :
    (Bᴴ * B).charpoly = ∏ i, (X - C (((hB.eigenvalues i) ^ 2 : ℝ) : ℂ)) := by
  have hsa : IsSelfAdjoint B := hB
  have h0 : cfc (fun x : ℝ => x ^ 2) B = B ^ 2 := cfc_pow_id (R := ℝ) B 2 hsa
  have h1 : Bᴴ * B = cfc (fun x : ℝ => x ^ 2) B := by rw [h0, hB.eq, sq]
  rw [h1, hB.charpoly_cfc_eq]
  simp

/-- The trace norm of a Hermitian matrix is the sum of the absolute values of its eigenvalues. -/
theorem traceNorm_of_isHermitian {B : Matrix (Fin n) (Fin n) ℂ} (hB : B.IsHermitian) :
    traceNorm B = ∑ i, |hB.eigenvalues i| := by
  have h := sum_eigenvalues_of_charpoly_eq (Matrix.isHermitian_conjTranspose_mul_self B)
    (fun i => (hB.eigenvalues i) ^ 2) (charpoly_conjTranspose_mul_self hB) Real.sqrt
  rw [traceNorm, h]
  exact Finset.sum_congr rfl fun i _ => Real.sqrt_sq_eq_abs _

/-- `cfc f A` is Hermitian whenever `A` is. -/
theorem isHermitian_cfc (f : ℝ → ℝ) {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) :
    (cfc f A).IsHermitian := by
  have hsa : IsSelfAdjoint A := hA
  have : IsSelfAdjoint (cfc f A) := cfc_predicate (R := ℝ) f A
  exact this

theorem isHermitian_cosMat {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) :
    (cosMat A).IsHermitian := isHermitian_cfc _ hA

theorem isHermitian_sinMat {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) :
    (sinMat A).IsHermitian := isHermitian_cfc _ hA

/-- Any real function of the eigenvalues of `cfc f A` sums to the corresponding function of the
values `f (eigenvalue i)`. -/
theorem sum_eigenvalues_cfc (f g : ℝ → ℝ) {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) :
    ∑ i, g ((isHermitian_cfc f hA).eigenvalues i) = ∑ i, g (f (hA.eigenvalues i)) :=
  sum_eigenvalues_of_charpoly_eq (isHermitian_cfc f hA) (fun i => f (hA.eigenvalues i))
    (hA.charpoly_cfc_eq f) g

/-- The trace norm of `cos A` is the sum of `|cos λᵢ|` over the eigenvalues `λᵢ` of `A`. -/
theorem traceNorm_cosMat {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) :
    traceNorm (cosMat A) = ∑ i, |Real.cos (hA.eigenvalues i)| := by
  rw [traceNorm_of_isHermitian (isHermitian_cosMat hA)]
  exact sum_eigenvalues_cfc Real.cos abs hA

/-- The trace norm of `sin A` is the sum of `|sin λᵢ|` over the eigenvalues `λᵢ` of `A`. -/
theorem traceNorm_sinMat {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) :
    traceNorm (sinMat A) = ∑ i, |Real.sin (hA.eigenvalues i)| := by
  rw [traceNorm_of_isHermitian (isHermitian_sinMat hA)]
  exact sum_eigenvalues_cfc Real.sin abs hA

/-- The trace of `cos A` is the sum of `cos λᵢ` over the eigenvalues `λᵢ` of `A`. -/
theorem trace_cosMat {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) :
    (cosMat A).trace = ((∑ i, Real.cos (hA.eigenvalues i) : ℝ) : ℂ) := by
  rw [(isHermitian_cosMat hA).trace_eq_sum_eigenvalues]
  have h := sum_eigenvalues_cfc Real.cos id hA
  simp only [id_eq] at h
  have h2 := congrArg (fun r : ℝ => (r : ℂ)) h
  push_cast at h2 ⊢
  exact h2

/-- **Upper trace-norm bound**: `‖cos A‖₁ ≤ n`. -/
theorem traceNorm_cosMat_le {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) :
    traceNorm (cosMat A) ≤ (n : ℝ) := by
  rw [traceNorm_cosMat hA]
  calc ∑ i, |Real.cos (hA.eigenvalues i)| ≤ ∑ _i : Fin n, (1 : ℝ) :=
        Finset.sum_le_sum fun i _ => Real.abs_cos_le_one _
    _ = (n : ℝ) := by simp

/-- **Lower trace-norm bound**: `‖cos A‖₁ ≥ n - (∑ λᵢ²)/2`. -/
theorem traceNorm_cosMat_ge {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) :
    (n : ℝ) - (∑ i, (hA.eigenvalues i) ^ 2) / 2 ≤ traceNorm (cosMat A) := by
  rw [traceNorm_cosMat hA]
  have h : ∀ i : Fin n, 1 - (hA.eigenvalues i) ^ 2 / 2 ≤ |Real.cos (hA.eigenvalues i)| :=
    fun i => le_trans (Real.one_sub_sq_div_two_le_cos) (le_abs_self _)
  calc (n : ℝ) - (∑ i, (hA.eigenvalues i) ^ 2) / 2
      = ∑ i, (1 - (hA.eigenvalues i) ^ 2 / 2) := by
        rw [Finset.sum_sub_distrib, ← Finset.sum_div]; simp
    _ ≤ ∑ i, |Real.cos (hA.eigenvalues i)| := Finset.sum_le_sum fun i _ => h i

/-- The trace of `cos A` is bounded in absolute value by its trace norm. -/
theorem norm_trace_cosMat_le_traceNorm {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) :
    ‖(cosMat A).trace‖ ≤ traceNorm (cosMat A) := by
  rw [trace_cosMat hA, traceNorm_cosMat hA, Complex.norm_real, Real.norm_eq_abs]
  exact Finset.abs_sum_le_sum_abs _ _

/-- **Combined cosine/sine trace-norm bound**: `‖cos A‖₁ + ‖sin A‖₁ ≥ n`. -/
theorem card_le_traceNorm_cosMat_add_traceNorm_sinMat {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian) : (n : ℝ) ≤ traceNorm (cosMat A) + traceNorm (sinMat A) := by
  rw [traceNorm_cosMat hA, traceNorm_sinMat hA, ← Finset.sum_add_distrib]
  have h : ∀ i : Fin n,
      (1 : ℝ) ≤ |Real.cos (hA.eigenvalues i)| + |Real.sin (hA.eigenvalues i)| := by
    intro i
    set x := hA.eigenvalues i
    have hc : Real.cos x ^ 2 ≤ |Real.cos x| := by
      rw [← sq_abs (Real.cos x)]
      exact pow_le_of_le_one (abs_nonneg _) (Real.abs_cos_le_one x) (by norm_num)
    have hs : Real.sin x ^ 2 ≤ |Real.sin x| := by
      rw [← sq_abs (Real.sin x)]
      exact pow_le_of_le_one (abs_nonneg _) (Real.abs_sin_le_one x) (by norm_num)
    have := Real.sin_sq_add_cos_sq x
    linarith
  calc (n : ℝ) = ∑ _i : Fin n, (1 : ℝ) := by simp
    _ ≤ _ := Finset.sum_le_sum fun i _ => h i

/-- **`CosTraceNorm3001`**: trace-norm bounds for the cosine of a Hermitian matrix.

For every Hermitian `n × n` complex matrix `A`, writing `cos A` for the matrix obtained from `A`
by the continuous functional calculus and `‖·‖₁` for the trace norm (sum of singular values):

* `‖cos A‖₁ ≤ n`;
* `n - (∑ λᵢ²)/2 ≤ ‖cos A‖₁`, where the `λᵢ` are the eigenvalues of `A`;
* `‖tr (cos A)‖ ≤ ‖cos A‖₁`;
* `n ≤ ‖cos A‖₁ + ‖sin A‖₁`. -/
theorem CosTraceNorm3001 (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) :
    traceNorm (cosMat A) ≤ (n : ℝ) ∧
    (n : ℝ) - (∑ i, (hA.eigenvalues i) ^ 2) / 2 ≤ traceNorm (cosMat A) ∧
    ‖(cosMat A).trace‖ ≤ traceNorm (cosMat A) ∧
    (n : ℝ) ≤ traceNorm (cosMat A) + traceNorm (sinMat A) :=
  ⟨traceNorm_cosMat_le hA, traceNorm_cosMat_ge hA, norm_trace_cosMat_le_traceNorm hA,
    card_le_traceNorm_cosMat_add_traceNorm_sinMat hA⟩

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

