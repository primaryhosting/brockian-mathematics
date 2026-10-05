/-!
# Cos Trace Norm 2707
Category: Brockian Corpus
Target: Brockian.CosTraceNorm2707
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Matrix

open NormedSpace (exp)

/-!
# Trace-norm bounds for matrix trigonometric functions

For an `n × n` complex matrix `A` we define the matrix cosine and matrix sine through the
matrix exponential,
`cos A = (exp (i A) + exp (-i A)) / 2` and `sin A = (exp (i A) - exp (-i A)) / (2 i)`.

The main results (`CosTraceNorm2707` and friends) bound the absolute value of the trace of these
matrices by the size `n` of the matrix, whenever `A` is Hermitian.  The proof goes through the
observation that `exp (± i A)` is unitary for Hermitian `A`, so that all of its entries have
absolute value at most `1`.
-/

namespace Brockian

variable {n : ℕ}

/-- The matrix cosine of a square complex matrix, defined through the matrix exponential by
`cos A = (exp (i A) + exp (-i A)) / 2`. -/
noncomputable def cosM (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (2 : ℂ)⁻¹ • (exp (Complex.I • A) + exp (-(Complex.I • A)))

/-- The matrix sine of a square complex matrix, defined through the matrix exponential by
`sin A = (exp (i A) - exp (-i A)) / (2 i)`. -/
noncomputable def sinM (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (2 * Complex.I)⁻¹ • (exp (Complex.I • A) - exp (-(Complex.I • A)))

/-- If `Uᴴ * U = 1` then every entry of `U` has norm at most `1`. -/
lemma norm_entry_le_one_of_conjTranspose_mul {U : Matrix (Fin n) (Fin n) ℂ}
    (h : Uᴴ * U = 1) (i j : Fin n) : ‖U i j‖ ≤ 1 := by
  have h1 : (Uᴴ * U) j j = 1 := by rw [h]; simp
  rw [Matrix.mul_apply] at h1
  simp only [Matrix.conjTranspose_apply, RCLike.star_def, RCLike.conj_mul] at h1
  have h2 : ((∑ k, ‖U k j‖ ^ 2 : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by push_cast; exact h1
  have h2' : ∑ k, ‖U k j‖ ^ 2 = (1 : ℝ) := Complex.ofReal_inj.mp h2
  have h3 : ‖U i j‖ ^ 2 ≤ 1 := by
    rw [← h2']
    exact Finset.single_le_sum (f := fun k => ‖U k j‖ ^ 2) (fun k _ => sq_nonneg _)
      (Finset.mem_univ i)
  nlinarith [norm_nonneg (U i j)]

/-- A matrix all of whose entries have norm at most `1` has trace of norm at most `n`. -/
lemma norm_trace_le_of_norm_entries {U : Matrix (Fin n) (Fin n) ℂ}
    (h : ∀ i j, ‖U i j‖ ≤ 1) : ‖U.trace‖ ≤ n := by
  rw [Matrix.trace]
  calc ‖∑ i, U.diag i‖ ≤ ∑ i : Fin n, ‖U.diag i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum fun i _ => h i i
    _ = n := by simp

/-- If `Uᴴ * U = 1` then the trace of `U` has norm at most the size of the matrix. -/
lemma norm_trace_le_of_conjTranspose_mul {U : Matrix (Fin n) (Fin n) ℂ}
    (h : Uᴴ * U = 1) : ‖U.trace‖ ≤ n :=
  norm_trace_le_of_norm_entries (norm_entry_le_one_of_conjTranspose_mul h)

/-- For a Hermitian matrix `A`, the matrix `exp (i A)` is unitary. -/
lemma conjTranspose_mul_exp_I_smul {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) :
    (exp (Complex.I • A))ᴴ * exp (Complex.I • A) = 1 := by
  have h1 : (Complex.I • A)ᴴ = -(Complex.I • A) := by
    rw [Matrix.conjTranspose_smul, hA.eq]; simp
  have h2 : (exp (Complex.I • A))ᴴ = exp (-(Complex.I • A)) := by
    rw [← h1, Matrix.exp_conjTranspose]
  rw [h2, Matrix.exp_neg]
  exact Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.isUnit_exp _))

/-- For a Hermitian matrix `A`, the matrix `exp (-i A)` is unitary as well. -/
lemma conjTranspose_mul_exp_neg_I_smul {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) :
    (exp (-(Complex.I • A)))ᴴ * exp (-(Complex.I • A)) = 1 := by
  have h : (-A).IsHermitian := hA.neg
  have := conjTranspose_mul_exp_I_smul h
  rwa [smul_neg] at this

/-- For Hermitian `A`, the trace of `exp (i A)` has norm at most `n`. -/
lemma norm_trace_exp_I_smul_le {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) :
    ‖(exp (Complex.I • A)).trace‖ ≤ n :=
  norm_trace_le_of_conjTranspose_mul (conjTranspose_mul_exp_I_smul hA)

/-- For Hermitian `A`, the trace of `exp (-i A)` has norm at most `n`. -/
lemma norm_trace_exp_neg_I_smul_le {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) :
    ‖(exp (-(Complex.I • A))).trace‖ ≤ n :=
  norm_trace_le_of_conjTranspose_mul (conjTranspose_mul_exp_neg_I_smul hA)

/-- The trace of the matrix cosine, expanded through the matrix exponential. -/
lemma trace_cosM (A : Matrix (Fin n) (Fin n) ℂ) :
    (cosM A).trace =
      (2 : ℂ)⁻¹ * ((exp (Complex.I • A)).trace + (exp (-(Complex.I • A))).trace) := by
  rw [cosM, Matrix.trace_smul, Matrix.trace_add, smul_eq_mul]

/-- The trace of the matrix sine, expanded through the matrix exponential. -/
lemma trace_sinM (A : Matrix (Fin n) (Fin n) ℂ) :
    (sinM A).trace =
      (2 * Complex.I)⁻¹ * ((exp (Complex.I • A)).trace - (exp (-(Complex.I • A))).trace) := by
  rw [sinM, Matrix.trace_smul, Matrix.trace_sub, smul_eq_mul]

/-- **Trace-norm bound for the matrix cosine.**  For a Hermitian `n × n` complex matrix `A`,
the trace of `cos A` has absolute value at most `n`. -/
theorem CosTraceNorm2707 {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) :
    ‖(cosM A).trace‖ ≤ n := by
  have h1 := norm_trace_exp_I_smul_le hA
  have h2 := norm_trace_exp_neg_I_smul_le hA
  rw [trace_cosM, norm_mul]
  have hnorm : ‖(2 : ℂ)⁻¹‖ = 1 / 2 := by
    rw [norm_inv]; simp
  have hsum : ‖(exp (Complex.I • A)).trace + (exp (-(Complex.I • A))).trace‖ ≤ (n : ℝ) + n :=
    (norm_add_le _ _).trans (add_le_add h1 h2)
  rw [hnorm]
  nlinarith [norm_nonneg ((exp (Complex.I • A)).trace + (exp (-(Complex.I • A))).trace)]

/-- **Trace-norm bound for the matrix sine.**  For a Hermitian `n × n` complex matrix `A`,
the trace of `sin A` has absolute value at most `n`. -/
theorem SinTraceNorm2707 {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) :
    ‖(sinM A).trace‖ ≤ n := by
  have h1 := norm_trace_exp_I_smul_le hA
  have h2 := norm_trace_exp_neg_I_smul_le hA
  rw [trace_sinM, norm_mul]
  have hnorm : ‖(2 * Complex.I)⁻¹‖ = 1 / 2 := by
    rw [norm_inv, norm_mul]; simp
  have hsum : ‖(exp (Complex.I • A)).trace - (exp (-(Complex.I • A))).trace‖ ≤ (n : ℝ) + n :=
    (norm_sub_le _ _).trans (add_le_add h1 h2)
  rw [hnorm]
  nlinarith [norm_nonneg ((exp (Complex.I • A)).trace - (exp (-(Complex.I • A))).trace)]

/-- For Hermitian `A`, the conjugate transpose of `exp (i A)` is `exp (-i A)`. -/
lemma conjTranspose_exp_I_smul {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) :
    (exp (Complex.I • A))ᴴ = exp (-(Complex.I • A)) := by
  have h1 : (Complex.I • A)ᴴ = -(Complex.I • A) := by
    rw [Matrix.conjTranspose_smul, hA.eq]; simp
  rw [← h1, Matrix.exp_conjTranspose]

/-- For Hermitian `A`, the matrix cosine is the Hermitian part of the unitary `exp (i A)`. -/
lemma cosM_eq_half_add_conjTranspose {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) :
    cosM A = (2 : ℂ)⁻¹ • (exp (Complex.I • A) + (exp (Complex.I • A))ᴴ) := by
  rw [cosM, conjTranspose_exp_I_smul hA]

/-- The matrix cosine of a Hermitian matrix is Hermitian. -/
lemma isHermitian_cosM {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) :
    (cosM A).IsHermitian := by
  rw [Matrix.IsHermitian, cosM_eq_half_add_conjTranspose hA, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose, add_comm]
  norm_num

/-- The matrix sine of a Hermitian matrix is Hermitian. -/
lemma isHermitian_sinM {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) :
    (sinM A).IsHermitian := by
  rw [Matrix.IsHermitian, sinM, ← conjTranspose_exp_I_smul hA, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose]
  rw [show star ((2 * Complex.I)⁻¹) = -(2 * Complex.I)⁻¹ by simp [mul_comm]]
  rw [neg_smul, ← smul_neg, neg_sub]

/-- The trace of the matrix cosine of a Hermitian matrix is real. -/
lemma trace_cosM_im {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) :
    (cosM A).trace.im = 0 := by
  have h : ((cosM A)ᴴ).trace = (cosM A).trace := by rw [(isHermitian_cosM hA).eq]
  rw [Matrix.trace_conjTranspose] at h
  exact Complex.conj_eq_iff_im.mp h

/-- The trace of the matrix sine of a Hermitian matrix is real. -/
lemma trace_sinM_im {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) :
    (sinM A).trace.im = 0 := by
  have h : ((sinM A)ᴴ).trace = (sinM A).trace := by rw [(isHermitian_sinM hA).eq]
  rw [Matrix.trace_conjTranspose] at h
  exact Complex.conj_eq_iff_im.mp h

/-- **Two-sided trace bound for the matrix cosine.**  For a Hermitian `n × n` complex matrix `A`,
the (real) trace of `cos A` lies in `[-n, n]`. -/
theorem CosTraceNorm2707_re {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) :
    -(n : ℝ) ≤ (cosM A).trace.re ∧ (cosM A).trace.re ≤ n := by
  have h := CosTraceNorm2707 hA
  have h1 : |(cosM A).trace.re| ≤ ‖(cosM A).trace‖ := Complex.abs_re_le_norm _
  constructor <;> [linarith [abs_le.mp (h1.trans h) |>.1]; linarith [abs_le.mp (h1.trans h) |>.2]]

/-- **Two-sided trace bound for the matrix sine.** -/
theorem SinTraceNorm2707_re {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) :
    -(n : ℝ) ≤ (sinM A).trace.re ∧ (sinM A).trace.re ≤ n := by
  have h := SinTraceNorm2707 hA
  have h1 : |(sinM A).trace.re| ≤ ‖(sinM A).trace‖ := Complex.abs_re_le_norm _
  constructor <;> [linarith [abs_le.mp (h1.trans h) |>.1]; linarith [abs_le.mp (h1.trans h) |>.2]]

/-- The matrix cosine of the zero matrix is the identity. -/
lemma cosM_zero : cosM (0 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  rw [cosM, smul_zero, neg_zero, NormedSpace.exp_zero]
  match_scalars; norm_num

/-- The bound `CosTraceNorm2707` is sharp: it is attained at `A = 0`. -/
theorem CosTraceNorm2707_sharp : ‖(cosM (0 : Matrix (Fin n) (Fin n) ℂ)).trace‖ = n := by
  rw [cosM_zero]
  simp

end Brockian


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

