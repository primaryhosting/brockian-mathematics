/-
# Cos Trace Norm 2003
Category: Brockian Corpus
Target: Brockian.CosTraceNorm2003
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Cos Trace Norm 2003
Category: Brockian Corpus
Target: Brockian.CosTraceNorm2003
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped ComplexOrder

namespace Brockian

open Matrix Finset

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The `i`-th singular value of a complex square matrix `A`: the square root of the `i`-th
eigenvalue of the positive semidefinite matrix `Aᴴ * A`. -/
noncomputable def singularValue (A : Matrix n n ℂ) (i : n) : ℝ :=
  Real.sqrt ((isHermitian_conjTranspose_mul_self A).eigenvalues i)

/-- The trace norm (Schatten `1`-norm, nuclear norm) of a complex square matrix: the sum of its
singular values. -/
noncomputable def traceNorm (A : Matrix n n ℂ) : ℝ := ∑ i, singularValue A i

lemma singularValue_nonneg (A : Matrix n n ℂ) (i : n) : 0 ≤ singularValue A i :=
  Real.sqrt_nonneg _

lemma traceNorm_nonneg (A : Matrix n n ℂ) : 0 ≤ traceNorm A :=
  Finset.sum_nonneg fun i _ => singularValue_nonneg A i

lemma singularValue_sq (A : Matrix n n ℂ) (i : n) :
    singularValue A i ^ 2 = (isHermitian_conjTranspose_mul_self A).eigenvalues i :=
  Real.sq_sqrt ((posSemidef_conjTranspose_mul_self A).eigenvalues_nonneg i)

/-- The `i`-th vector of the chosen orthonormal eigenbasis of `Aᴴ * A`, as a plain function. -/
noncomputable def evec (A : Matrix n n ℂ) (i : n) : n → ℂ :=
  ((isHermitian_conjTranspose_mul_self A).eigenvectorBasis i).ofLp

lemma evec_dotProduct_self (A : Matrix n n ℂ) (i : n) :
    star (evec A i) ⬝ᵥ evec A i = 1 := by
  set hB := isHermitian_conjTranspose_mul_self A
  have h := hB.eigenvectorBasis.orthonormal.1 i
  have h2 := EuclideanSpace.inner_eq_star_dotProduct
    (hB.eigenvectorBasis i) (hB.eigenvectorBasis i)
  rw [inner_self_eq_norm_sq_to_K, h] at h2
  rw [evec, dotProduct_comm]
  simp [← h2]

omit [DecidableEq n] in
lemma dotProduct_conjTranspose_mul (A : Matrix n n ℂ) (v : n → ℂ) :
    star (A *ᵥ v) ⬝ᵥ (A *ᵥ v) = star v ⬝ᵥ ((Aᴴ * A) *ᵥ v) := by
  rw [star_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_vecMul, ← dotProduct_mulVec,
    mulVec_mulVec]

lemma dotProduct_mulVec_evec_self (A : Matrix n n ℂ) (i : n) :
    star (A *ᵥ evec A i) ⬝ᵥ (A *ᵥ evec A i) = ((singularValue A i ^ 2 : ℝ) : ℂ) := by
  rw [dotProduct_conjTranspose_mul, evec,
    (isHermitian_conjTranspose_mul_self A).mulVec_eigenvectorBasis i,
    dotProduct_smul, ← evec, evec_dotProduct_self, singularValue_sq]
  simp

/-- The Euclidean norm of `A` applied to the `i`-th eigenvector of `Aᴴ A` is the `i`-th singular
value of `A`. -/
lemma norm_mulVec_evec (A : Matrix n n ℂ) (i : n) :
    ‖(WithLp.toLp 2 (A *ᵥ evec A i) : EuclideanSpace ℂ n)‖ = singularValue A i := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), EuclideanSpace.inner_eq_star_dotProduct]
  rw [dotProduct_comm, dotProduct_mulVec_evec_self,
    show RCLike.re ((singularValue A i ^ 2 : ℝ) : ℂ) = singularValue A i ^ 2 from
      Complex.ofReal_re _]
  exact Real.sqrt_sq (singularValue_nonneg A i)

lemma norm_evec_toLp (A : Matrix n n ℂ) (i : n) :
    ‖(WithLp.toLp 2 (evec A i) : EuclideanSpace ℂ n)‖ = 1 := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), EuclideanSpace.inner_eq_star_dotProduct]
  rw [dotProduct_comm, evec_dotProduct_self]
  simp

omit [DecidableEq n] in
/-- Cauchy-Schwarz for the (conjugated) dot product on `n → ℂ`. -/
lemma norm_dotProduct_le (a b : n → ℂ) :
    ‖star a ⬝ᵥ b‖ ≤ ‖(WithLp.toLp 2 a : EuclideanSpace ℂ n)‖ *
      ‖(WithLp.toLp 2 b : EuclideanSpace ℂ n)‖ := by
  have h := norm_inner_le_norm (𝕜 := ℂ) (WithLp.toLp 2 a : EuclideanSpace ℂ n) (WithLp.toLp 2 b)
  rw [EuclideanSpace.inner_eq_star_dotProduct] at h
  simpa [dotProduct_comm] using h

/-- Each diagonal entry of `A` in the eigenbasis of `Aᴴ A` is bounded by the corresponding
singular value. -/
lemma norm_evec_diag_le (A : Matrix n n ℂ) (i : n) :
    ‖star (evec A i) ⬝ᵥ (A *ᵥ evec A i)‖ ≤ singularValue A i := by
  have h := norm_dotProduct_le (evec A i) (A *ᵥ evec A i)
  rwa [norm_evec_toLp, norm_mulVec_evec, one_mul] at h

omit [DecidableEq n] in
lemma conjTranspose_mul_mul_apply_diag (M U : Matrix n n ℂ) (i : n) :
    (Uᴴ * M * U) i i = star (fun k => U k i) ⬝ᵥ (M *ᵥ (fun k => U k i)) := by
  simp [Matrix.mul_apply, dotProduct, mulVec, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp [mul_comm, mul_assoc, mul_left_comm]

lemma trace_eq_sum_evec_diag (A : Matrix n n ℂ) :
    A.trace = ∑ i, star (evec A i) ⬝ᵥ (A *ᵥ evec A i) := by
  set hB := isHermitian_conjTranspose_mul_self A
  set U : Matrix n n ℂ := (hB.eigenvectorUnitary : Matrix n n ℂ) with hUdef
  have hUU : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 (hB.eigenvectorUnitary).2
  have hcol : ∀ i : n, (fun k => U k i) = evec A i := by
    intro i
    funext k
    simp [hUdef, evec]
  have htr : (Uᴴ * A * U).trace = A.trace := by
    rw [Matrix.trace_mul_cycle, hUU, Matrix.one_mul]
  rw [← htr, Matrix.trace]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply]
  rw [conjTranspose_mul_mul_apply_diag, hcol]

/-- **Trace bound**: the absolute value of the trace of a complex square matrix is at most its
trace norm, `|tr A| ≤ ‖A‖₁`. -/
theorem norm_trace_le_traceNorm (A : Matrix n n ℂ) : ‖A.trace‖ ≤ traceNorm A := by
  rw [trace_eq_sum_evec_diag A, traceNorm]
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun i _ => norm_evec_diag_le A i)

omit [DecidableEq n] in
/-- The trace of `Aᴴ * A` is the sum of the squared moduli of the entries of `A`. -/
lemma trace_conjTranspose_mul_self (A : Matrix n n ℂ) :
    (Aᴴ * A).trace = ((∑ i, ∑ j, ‖A i j‖ ^ 2 : ℝ) : ℂ) := by
  rw [Matrix.trace]
  push_cast
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def, Complex.conj_mul']

/-- The sum of the squares of the singular values of `A` is the squared Frobenius norm. -/
lemma sum_singularValue_sq (A : Matrix n n ℂ) :
    ∑ i, singularValue A i ^ 2 = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  have h := (isHermitian_conjTranspose_mul_self A).trace_eq_sum_eigenvalues
  rw [trace_conjTranspose_mul_self A] at h
  have h' : ((∑ i, ∑ j, ‖A i j‖ ^ 2 : ℝ) : ℂ) =
      ((∑ i, (isHermitian_conjTranspose_mul_self A).eigenvalues i : ℝ) : ℂ) := by
    rw [h]; push_cast; rfl
  have h'' : (∑ i, ∑ j, ‖A i j‖ ^ 2 : ℝ) =
      ∑ i, (isHermitian_conjTranspose_mul_self A).eigenvalues i := by
    exact_mod_cast h'
  simp only [singularValue_sq]
  exact h''.symm

/-- **Frobenius vs. trace norm.**  The Frobenius (Hilbert-Schmidt) norm of a matrix is at most
its trace norm. -/
theorem frobenius_le_traceNorm (A : Matrix n n ℂ) :
    Real.sqrt (∑ i, ∑ j, ‖A i j‖ ^ 2) ≤ traceNorm A := by
  rw [← sum_singularValue_sq]
  exact (Real.sqrt_le_left (traceNorm_nonneg A)).mpr
    (Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => singularValue_nonneg A i)

/-- Sanity check: the trace norm of the `1 × 1` matrix `(z)` is `‖z‖`. -/
lemma traceNorm_fin_one (z : ℂ) : traceNorm (!![z] : Matrix (Fin 1) (Fin 1) ℂ) = ‖z‖ := by
  have hsq := sum_singularValue_sq (!![z] : Matrix (Fin 1) (Fin 1) ℂ)
  simp only [Finset.univ_unique, Finset.sum_singleton] at hsq
  have h0 : singularValue (!![z] : Matrix (Fin 1) (Fin 1) ℂ) 0 ^ 2 = ‖z‖ ^ 2 := by
    simpa using hsq
  have := abs_eq_abs.2 (Or.inl (pow_left_injective (by norm_num) (by norm_num) ?_))
  · exact this
  · exact h0

/-- **Cos trace norm bound (2003).**  For every complex square matrix `A` and every phase `θ`,
the real part of `e^{iθ} · tr A`, namely `cos θ · Re(tr A) - sin θ · Im(tr A)`, is bounded above
by the trace norm (nuclear norm) `‖A‖₁ = ∑ σᵢ(A)`.  Taking the supremum over `θ` recovers the
sharp bound `|tr A| ≤ ‖A‖₁`. -/
theorem CosTraceNorm2003 (A : Matrix n n ℂ) (θ : ℝ) :
    Real.cos θ * (A.trace).re - Real.sin θ * (A.trace).im ≤ traceNorm A := by
  have hexp : Complex.exp (θ * Complex.I) = (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I := by
    rw [Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
  have hre : Real.cos θ * (A.trace).re - Real.sin θ * (A.trace).im
      = (Complex.exp (θ * Complex.I) * A.trace).re := by
    rw [hexp]
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  rw [hre]
  refine le_trans (Complex.re_le_norm _) ?_
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  exact norm_trace_le_traceNorm A

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

