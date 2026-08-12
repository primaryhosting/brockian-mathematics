import Mathlib

/-!
# Trace-norm bounds for the matrix cosine and sine (`CosTraceNorm` family)

This file develops, from scratch, the Schatten 1-norm (trace norm) of a complex square matrix,
the Hermitian functional calculus `Brockian.hermFun`, and proves a family of trace-norm bounds
for the matrix cosine and sine of a Hermitian matrix.
-/

set_option maxRecDepth 8000

open scoped BigOperators
open Matrix Polynomial

namespace Brockian

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The trace norm (Schatten 1-norm) of a complex square matrix: the sum of its singular
values, i.e. the sum of the square roots of the eigenvalues of `Aᴴ * A`. -/
noncomputable def traceNorm (A : Matrix n n ℂ) : ℝ :=
  ∑ i, Real.sqrt ((Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues i)

/-- The Hermitian functional calculus: `hermFun hA f` is `f` applied to the Hermitian matrix `A`
through its spectral decomposition. -/
noncomputable def hermFun {A : Matrix n n ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) : Matrix n n ℂ :=
  Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) hA.eigenvectorUnitary
    (Matrix.diagonal fun i => ((f (hA.eigenvalues i) : ℝ) : ℂ))

/-- The cosine of a Hermitian matrix. -/
noncomputable def cosMat {A : Matrix n n ℂ} (hA : A.IsHermitian) : Matrix n n ℂ :=
  hermFun hA Real.cos

/-- The sine of a Hermitian matrix. -/
noncomputable def sinMat {A : Matrix n n ℂ} (hA : A.IsHermitian) : Matrix n n ℂ :=
  hermFun hA Real.sin

/-- The eigenvalue function of a Hermitian matrix is determined, as a multiset, by the
characteristic polynomial. -/
lemma sum_eigenvalues_of_charpoly {A : Matrix n n ℂ} (hA : A.IsHermitian) (μ : n → ℝ)
    (h : A.charpoly = ∏ i, (X - C ((μ i : ℝ) : ℂ))) (f : ℝ → ℝ) :
    ∑ i, f (hA.eigenvalues i) = ∑ i, f (μ i) := by
  have hroots : A.charpoly.roots = Multiset.map (fun i => ((μ i : ℝ) : ℂ)) Finset.univ.val := by
    rw [h, Polynomial.roots_prod]
    · simp
    · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]
  have h2 := hA.roots_charpoly_eq_eigenvalues
  rw [hroots] at h2
  have h3 : Multiset.map (fun i => hA.eigenvalues i) Finset.univ.val
      = Multiset.map (fun i => μ i) Finset.univ.val := by
    have := congrArg (Multiset.map Complex.re) h2.symm
    simpa [Multiset.map_map, Function.comp_def] using this
  have h4 := congrArg (fun m => (Multiset.map f m).sum) h3
  simp only [Multiset.map_map, Function.comp_def] at h4
  rw [Finset.sum_eq_multiset_sum, Finset.sum_eq_multiset_sum]
  exact h4

/-- Conjugating a real diagonal matrix by a unitary does not change the characteristic
polynomial. -/
lemma charpoly_conj (U : Matrix.unitaryGroup n ℂ) (d : n → ℝ) :
    (Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) U
      (Matrix.diagonal fun i => ((d i : ℝ) : ℂ))).charpoly = ∏ i, (X - C ((d i : ℝ) : ℂ)) := by
  rw [Unitary.conjStarAlgAut_apply, Matrix.charpoly_mul_comm, ← mul_assoc,
    Unitary.coe_star_mul_self, one_mul, Matrix.charpoly_diagonal]

/-- The trace norm computed from a list of "signed singular values". -/
lemma traceNorm_of_charpoly {M : Matrix n n ℂ} (μ : n → ℝ)
    (h : (Mᴴ * M).charpoly = ∏ i, (X - C (((μ i) ^ 2 : ℝ) : ℂ))) :
    traceNorm M = ∑ i, |μ i| := by
  have := sum_eigenvalues_of_charpoly (Matrix.isHermitian_conjTranspose_mul_self M)
    (fun i => (μ i) ^ 2) h Real.sqrt
  rw [traceNorm, this]
  exact Finset.sum_congr rfl fun i _ => Real.sqrt_sq_eq_abs _

lemma hermFun_isHermitian {A : Matrix n n ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (hermFun hA f).IsHermitian := by
  have : star (hermFun hA f) = hermFun hA f := by
    rw [hermFun, ← map_star]
    congr 1
    rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
    simp
  simp [Matrix.star_eq_conjTranspose] at this
  exact this

lemma hermFun_mul {A : Matrix n n ℂ} (hA : A.IsHermitian) (f g : ℝ → ℝ) :
    hermFun hA f * hermFun hA g = hermFun hA (fun x => f x * g x) := by
  rw [hermFun, hermFun, hermFun, ← map_mul, Matrix.diagonal_mul_diagonal]
  simp

lemma hermFun_one {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    hermFun hA (fun _ => 1) = 1 := by
  rw [hermFun]
  simp only [Complex.ofReal_one, Matrix.diagonal_one]
  exact map_one (Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) hA.eigenvectorUnitary)

lemma hermFun_sub {A : Matrix n n ℂ} (hA : A.IsHermitian) (f g : ℝ → ℝ) :
    hermFun hA f - hermFun hA g = hermFun hA (fun x => f x - g x) := by
  rw [hermFun, hermFun, hermFun, ← map_sub]
  congr 1
  ext i j
  by_cases h : i = j <;> simp [h]

lemma hermFun_id {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    hermFun hA (fun x => x) = A := by
  conv_rhs => rw [hA.spectral_theorem]
  rfl

/-- The trace norm of `f` applied to a Hermitian matrix is `∑ |f (λ i)|`. -/
lemma traceNorm_hermFun {A : Matrix n n ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    traceNorm (hermFun hA f) = ∑ i, |f (hA.eigenvalues i)| := by
  refine traceNorm_of_charpoly (fun i => f (hA.eigenvalues i)) ?_
  have hH : (hermFun hA f)ᴴ = hermFun hA f :=
    (hermFun_isHermitian hA f)
  rw [hH, hermFun_mul]
  have := charpoly_conj hA.eigenvectorUnitary (fun i => f (hA.eigenvalues i) * f (hA.eigenvalues i))
  rw [hermFun]
  simp only [sq]
  convert this using 3

/-- The trace norm of a Hermitian matrix is the sum of the absolute values of its
eigenvalues. -/
lemma traceNorm_of_isHermitian {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    traceNorm A = ∑ i, |hA.eigenvalues i| := by
  conv_lhs => rw [← hermFun_id hA]
  rw [traceNorm_hermFun]

/-- The trace norm of `A * A`, for `A` Hermitian, is the sum of the squares of the
eigenvalues (the squared Frobenius norm). -/
lemma traceNorm_sq_of_isHermitian {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    traceNorm (A * A) = ∑ i, (hA.eigenvalues i) ^ 2 := by
  have h : A * A = hermFun hA (fun x => x * x) := by
    rw [← hermFun_mul, hermFun_id]
  rw [h, traceNorm_hermFun]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [abs_of_nonneg (mul_self_nonneg _), sq]

lemma traceNorm_nonneg (A : Matrix n n ℂ) : 0 ≤ traceNorm A :=
  Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _

/-- Sanity check: the trace norm of the identity matrix is the size of the matrix. -/
lemma traceNorm_one : traceNorm (1 : Matrix n n ℂ) = (Fintype.card n : ℝ) := by
  have hH : (1 : Matrix n n ℂ).IsHermitian := Matrix.isHermitian_one
  rw [traceNorm_of_isHermitian hH]
  have hchar : (1 : Matrix n n ℂ).charpoly = ∏ _i : n, (X - C (((1 : ℝ) : ℂ))) := by
    rw [← Matrix.diagonal_one, Matrix.charpoly_diagonal]
    simp
  rw [sum_eigenvalues_of_charpoly hH (fun _ => (1 : ℝ)) hchar (fun x => |x|)]
  simp

/-- Sanity check: the matrix cosine and sine satisfy the Pythagorean identity. -/
lemma cosMat_sq_add_sinMat_sq {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    cosMat hA * cosMat hA + sinMat hA * sinMat hA = 1 := by
  rw [cosMat, sinMat, hermFun_mul, hermFun_mul, ← hermFun_one hA, hermFun, hermFun, hermFun,
    ← map_add]
  congr 1
  ext i j
  by_cases h : i = j
  · subst h
    have hpy := Real.sin_sq_add_cos_sq (hA.eigenvalues i)
    have : Real.cos (hA.eigenvalues i) * Real.cos (hA.eigenvalues i)
        + Real.sin (hA.eigenvalues i) * Real.sin (hA.eigenvalues i) = 1 := by nlinarith
    simp only [Matrix.add_apply, Matrix.diagonal_apply_eq]
    rw [← Complex.ofReal_add, this]
  · simp [h]

/-- `‖cos A‖₁ ≤ n` for a Hermitian `n × n` matrix `A`. -/
theorem CosTraceNorm2003_cos_le_card {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    traceNorm (cosMat hA) ≤ (Fintype.card n : ℝ) := by
  rw [cosMat, traceNorm_hermFun]
  calc ∑ i, |Real.cos (hA.eigenvalues i)| ≤ ∑ _i : n, (1 : ℝ) :=
        Finset.sum_le_sum fun _ _ => Real.abs_cos_le_one _
    _ = (Fintype.card n : ℝ) := by simp

/-- `‖sin A‖₁ ≤ ‖A‖₁` for a Hermitian matrix `A`. -/
theorem CosTraceNorm2003_sin_le_traceNorm {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    traceNorm (sinMat hA) ≤ traceNorm A := by
  rw [sinMat, traceNorm_hermFun, traceNorm_of_isHermitian hA]
  exact Finset.sum_le_sum fun _ _ => Real.abs_sin_le_abs

/-- `‖1 - cos A‖₁ ≤ ½ ‖A‖₂²` for a Hermitian matrix `A`. -/
theorem CosTraceNorm2003_one_sub_cos {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    traceNorm (1 - cosMat hA) ≤ (1 / 2) * traceNorm (A * A) := by
  have h1 : (1 : Matrix n n ℂ) - cosMat hA = hermFun hA (fun x => 1 - Real.cos x) := by
    rw [cosMat, ← hermFun_one hA, hermFun_sub]
  rw [h1, traceNorm_hermFun, traceNorm_sq_of_isHermitian hA, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have hc := Real.one_sub_sq_div_two_le_cos (x := hA.eigenvalues i)
  have hle : 1 - Real.cos (hA.eigenvalues i) ≤ 1 / 2 * (hA.eigenvalues i) ^ 2 := by linarith
  have hnn : 0 ≤ 1 - Real.cos (hA.eigenvalues i) := by
    have := Real.cos_le_one (hA.eigenvalues i); linarith
  rwa [abs_of_nonneg hnn]

/-- Scalar ingredient: `1 ≤ |cos x| + |sin x|`. -/
lemma one_le_abs_cos_add_abs_sin (x : ℝ) : 1 ≤ |Real.cos x| + |Real.sin x| := by
  have hc : Real.cos x ^ 2 ≤ |Real.cos x| := by
    nlinarith [abs_nonneg (Real.cos x), Real.abs_cos_le_one x, sq_abs (Real.cos x)]
  have hs : Real.sin x ^ 2 ≤ |Real.sin x| := by
    nlinarith [abs_nonneg (Real.sin x), Real.abs_sin_le_one x, sq_abs (Real.sin x)]
  have := Real.sin_sq_add_cos_sq x
  linarith

/-- Trace-norm lower bound: `n ≤ ‖cos A‖₁ + ‖sin A‖₁` for a Hermitian `n × n` matrix `A`. -/
theorem CosTraceNorm2003_card_le_cos_add_sin {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    (Fintype.card n : ℝ) ≤ traceNorm (cosMat hA) + traceNorm (sinMat hA) := by
  rw [cosMat, sinMat, traceNorm_hermFun, traceNorm_hermFun, ← Finset.sum_add_distrib]
  calc (Fintype.card n : ℝ) = ∑ _i : n, (1 : ℝ) := by simp
    _ ≤ ∑ i, (|Real.cos (hA.eigenvalues i)| + |Real.sin (hA.eigenvalues i)|) :=
        Finset.sum_le_sum fun i _ => one_le_abs_cos_add_abs_sin _

/-- **New trace-norm bounds for the matrix cosine and sine.**
For a Hermitian complex matrix `A`, with `‖·‖₁` the trace norm (Schatten 1-norm):
* `‖cos A‖₁ ≤ n`;
* `‖sin A‖₁ ≤ ‖A‖₁`;
* `‖1 - cos A‖₁ ≤ ½ ‖A‖₂²`, where `‖A‖₂² = ‖A * A‖₁` is the squared Frobenius norm;
* `n ≤ ‖cos A‖₁ + ‖sin A‖₁`. -/
theorem CosTraceNorm2003 {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    traceNorm (cosMat hA) ≤ (Fintype.card n : ℝ) ∧
    traceNorm (sinMat hA) ≤ traceNorm A ∧
    traceNorm (1 - cosMat hA) ≤ (1 / 2) * traceNorm (A * A) ∧
    (Fintype.card n : ℝ) ≤ traceNorm (cosMat hA) + traceNorm (sinMat hA) :=
  ⟨CosTraceNorm2003_cos_le_card hA, CosTraceNorm2003_sin_le_traceNorm hA,
    CosTraceNorm2003_one_sub_cos hA, CosTraceNorm2003_card_le_cos_add_sin hA⟩

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

