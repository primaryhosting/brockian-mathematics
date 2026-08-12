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

/-!
# The `CosTraceNorm` family: trace-norm bounds for Hermitian matrices

For a Hermitian matrix `A` the *trace norm* (Schatten 1-norm) `‖A‖₁` is the sum of the absolute
values of its eigenvalues.  This file develops a small family of bounds for it:

* `Brockian.CosTraceNorm2001` : `|Tr A| ≤ ‖A‖₁`;
* `Brockian.CosTraceNorm2002` : the dual (Hölder-type) bound `|Tr (A U)| ≤ ‖A‖₁` for `U` unitary;
* `Brockian.CosTraceNorm2003` : a new cosine-parametrised bound.  If `B` is a Hermitian unitary
  (a reflection), then for every angle `t`,
  `√((cos t · Tr A)² + (sin t · Tr (A B))²) ≤ ‖A‖₁`,
  i.e. the point `(Tr A, Tr (A B))` lies inside every ellipse `x²/sec²t + y²/csc²t = ‖A‖₁²`.
-/

namespace Brockian

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The **trace norm** (Schatten 1-norm) of a Hermitian matrix: the sum of the absolute values
of its eigenvalues. -/
noncomputable def traceNorm {A : Matrix n n ℂ} (hA : A.IsHermitian) : ℝ :=
  ∑ i, |hA.eigenvalues i|

lemma traceNorm_nonneg {A : Matrix n n ℂ} (hA : A.IsHermitian) : 0 ≤ traceNorm hA :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- Every diagonal entry of a unitary matrix has norm at most one. -/
lemma norm_diag_le_one_of_unitary {W : Matrix n n ℂ} (hW : Wᴴ * W = 1) (i : n) :
    ‖W i i‖ ≤ 1 := by
  have h : (Wᴴ * W) i i = 1 := by rw [hW]; simp
  rw [Matrix.mul_apply] at h
  have h2 : ∑ j, ((Complex.normSq (W j i) : ℝ) : ℂ) = 1 := by
    rw [← h]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [Matrix.conjTranspose_apply, Complex.normSq_eq_conj_mul_self]
  have h3 : ∑ j, Complex.normSq (W j i) = 1 := by exact_mod_cast h2
  have h4 : Complex.normSq (W i i) ≤ 1 := by
    rw [← h3]
    exact Finset.single_le_sum (f := fun j => Complex.normSq (W j i))
      (fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
  rw [Complex.norm_def]
  simpa using Real.sqrt_le_sqrt h4

/-- The trace of a diagonal matrix times an arbitrary matrix, bounded entrywise. -/
lemma norm_trace_diagonal_mul_le {W : Matrix n n ℂ} (f : n → ℝ) (hWd : ∀ i, ‖W i i‖ ≤ 1) :
    ‖((diagonal (RCLike.ofReal ∘ f) : Matrix n n ℂ) * W).trace‖ ≤ ∑ i, |f i| := by
  have h : ((diagonal (RCLike.ofReal ∘ f) : Matrix n n ℂ) * W).trace
      = ∑ i, (f i : ℂ) * W i i := by
    rw [Matrix.trace]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Matrix.diagonal_mul, Matrix.diag]
  rw [h]
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_mul, show ‖(f i : ℂ)‖ = |f i| by simp]
  nlinarith [abs_nonneg (f i), hWd i, norm_nonneg (W i i)]

/-- `CosTraceNorm2002`: the dual (Hölder-type) trace-norm bound: for a Hermitian matrix `A` and
any unitary matrix `U` we have `|Tr (A U)| ≤ ‖A‖₁`. -/
theorem CosTraceNorm2002 {A U : Matrix n n ℂ} (hA : A.IsHermitian) (hU : Uᴴ * U = 1) :
    ‖(A * U).trace‖ ≤ traceNorm hA := by
  set V : Matrix n n ℂ := (hA.eigenvectorUnitary : Matrix n n ℂ) with hVdef
  have hVV : star V * V = 1 := Unitary.coe_star_mul_self _
  have hVV' : V * star V = 1 := Unitary.coe_mul_star_self _
  set D : Matrix n n ℂ := diagonal (RCLike.ofReal ∘ hA.eigenvalues) with hD
  have hspec : A = V * D * star V := hA.spectral_theorem
  set W : Matrix n n ℂ := star V * U * V with hW
  have hstarW : star W = star V * star U * V := by
    rw [hW, Matrix.star_mul, Matrix.star_mul, star_star, mul_assoc]
  have hWu : Wᴴ * W = 1 := by
    have h1 : (Wᴴ : Matrix n n ℂ) = star W := rfl
    rw [h1, hstarW, hW]
    calc star V * star U * V * (star V * U * V)
        = star V * star U * (V * star V) * U * V := by simp [mul_assoc]
      _ = star V * (star U * U) * V := by rw [hVV']; simp [mul_assoc]
      _ = 1 := by rw [show (star U : Matrix n n ℂ) = Uᴴ from rfl, hU]; simpa using hVV
  have htr : (A * U).trace = (D * W).trace := by
    rw [hspec, hW, show V * D * star V * U = V * (D * star V * U) by simp [mul_assoc],
      Matrix.trace_mul_comm]
    congr 1
    simp [mul_assoc]
  rw [htr, hD, traceNorm]
  exact norm_trace_diagonal_mul_le _ (norm_diag_le_one_of_unitary hWu)

/-- `CosTraceNorm2001`: the trace of a Hermitian matrix is bounded by its trace norm. -/
theorem CosTraceNorm2001 {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    ‖A.trace‖ ≤ traceNorm hA := by
  have h := CosTraceNorm2002 (U := (1 : Matrix n n ℂ)) hA (by simp)
  simpa using h

omit [DecidableEq n] in
/-- The trace of a Hermitian matrix is real. -/
lemma trace_im_eq_zero {A : Matrix n n ℂ} (hA : A.IsHermitian) : (A.trace).im = 0 := by
  have h : star A.trace = A.trace := by rw [← Matrix.trace_conjTranspose, hA.eq]
  have := congrArg Complex.im h
  simp only [Complex.star_def, Complex.conj_im] at this
  linarith

omit [DecidableEq n] in
/-- The trace of a product of two Hermitian matrices is real. -/
lemma trace_mul_im_eq_zero {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ((A * B).trace).im = 0 := by
  have h : star ((A * B).trace) = (A * B).trace := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hA.eq, hB.eq, Matrix.trace_mul_comm]
  have := congrArg Complex.im h
  simp only [Complex.star_def, Complex.conj_im] at this
  linarith

/-- If `B` is a Hermitian unitary (a reflection) and `c² + s² = 1`, then
`c • 1 + (i s) • B` is unitary; this is `exp (i s B)` for a reflection `B`. -/
lemma isUnitary_cos_add_I_sin_smul {B : Matrix n n ℂ} (hB : B.IsHermitian) (hB2 : B * B = 1)
    (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) :
    ((c : ℂ) • (1 : Matrix n n ℂ) + (Complex.I * (s : ℂ)) • B)ᴴ *
      ((c : ℂ) • (1 : Matrix n n ℂ) + (Complex.I * (s : ℂ)) • B) = 1 := by
  have hBH : Bᴴ = B := hB.eq
  have key : ((c : ℂ) ^ 2 + (s : ℂ) ^ 2) = 1 := by
    exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) h
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hBH, Matrix.conjTranspose_one,
    Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one, hB2, star_mul', Complex.star_def, Complex.conj_I,
    Complex.conj_ofReal, smul_add, smul_smul]
  match_scalars
  · linear_combination key - ((s : ℂ) ^ 2) * Complex.I_sq
  · ring

/-- `CosTraceNorm2003`: a cosine-parametrised trace-norm bound.  If `A` is Hermitian and `B` is a
Hermitian unitary (a reflection: `Bᴴ = B` and `B * B = 1`), then for every angle `t` the point
`(cos t · Tr A, sin t · Tr (A B))` lies in the disc of radius `‖A‖₁`. -/
theorem CosTraceNorm2003 {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hB2 : B * B = 1) (t : ℝ) :
    Real.sqrt ((Real.cos t * (A.trace).re) ^ 2 + (Real.sin t * ((A * B).trace).re) ^ 2)
      ≤ traceNorm hA := by
  set c : ℝ := Real.cos t with hc
  set s : ℝ := Real.sin t with hs
  set U : Matrix n n ℂ := (c : ℂ) • (1 : Matrix n n ℂ) + (Complex.I * (s : ℂ)) • B with hU
  have hUu : Uᴴ * U = 1 :=
    isUnitary_cos_add_I_sin_smul hB hB2 c s (by rw [hc, hs]; exact Real.cos_sq_add_sin_sq t)
  have hbound := CosTraceNorm2002 hA hUu
  have hAtr : A.trace = ((A.trace).re : ℂ) := by
    apply Complex.ext <;> simp [trace_im_eq_zero hA]
  have hABtr : (A * B).trace = (((A * B).trace).re : ℂ) := by
    apply Complex.ext <;> simp [trace_mul_im_eq_zero hA hB]
  have htr : (A * U).trace
      = ((c * (A.trace).re : ℝ) : ℂ) + ((s * ((A * B).trace).re : ℝ) : ℂ) * Complex.I := by
    rw [hU, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one,
      Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul]
    rw [smul_eq_mul, smul_eq_mul]
    conv_lhs => rw [hAtr, hABtr]
    push_cast
    ring
  rw [htr, Complex.norm_add_mul_I] at hbound
  exact hbound

/-- Sanity check: the hypotheses of `CosTraceNorm2003` are satisfiable (`B = 1` is a reflection). -/
example {A : Matrix n n ℂ} (hA : A.IsHermitian) (t : ℝ) :
    Real.sqrt ((Real.cos t * (A.trace).re) ^ 2 + (Real.sin t * ((A * 1).trace).re) ^ 2)
      ≤ traceNorm hA :=
  CosTraceNorm2003 hA Matrix.isHermitian_one (by simp) t

end Brockian

#print axioms Brockian.CosTraceNorm2001
#print axioms Brockian.CosTraceNorm2002
#print axioms Brockian.CosTraceNorm2003

