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

namespace Brockian

open NormedSpace
open scoped Matrix Matrix.Norms.Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The matrix cosine of a complex square matrix, defined through the matrix exponential by
`cos A = (exp (i A) + exp (-i A)) / 2`. -/
noncomputable def cosMat (A : Matrix n n ℂ) : Matrix n n ℂ :=
  (2 : ℂ)⁻¹ • (exp (Complex.I • A) + exp (-(Complex.I • A)))

omit [Fintype n] [DecidableEq n] in
/-- If `A` is Hermitian then `i • A` is skew-adjoint. -/
lemma smul_I_mem_skewAdjoint {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    Complex.I • A ∈ skewAdjoint (Matrix n n ℂ) := by
  rw [skewAdjoint.mem_iff, star_smul, Matrix.star_eq_conjTranspose, hA.eq]
  simp

/-- For Hermitian `A`, the matrix `exp (i A)` is unitary. -/
lemma exp_I_smul_mem_unitary {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    exp (Complex.I • A) ∈ Matrix.unitaryGroup n ℂ :=
  exp_mem_unitary_of_mem_skewAdjoint (smul_I_mem_skewAdjoint hA)

/-- For Hermitian `A`, the matrix `exp (-i A)` is unitary. -/
lemma exp_neg_I_smul_mem_unitary {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    exp (-(Complex.I • A)) ∈ Matrix.unitaryGroup n ℂ :=
  exp_mem_unitary_of_mem_skewAdjoint (neg_mem (smul_I_mem_skewAdjoint hA))

/-- The trace of a unitary matrix has modulus at most the size of the matrix. -/
lemma norm_trace_le_card_of_mem_unitaryGroup {U : Matrix n n ℂ}
    (hU : U ∈ Matrix.unitaryGroup n ℂ) : ‖U.trace‖ ≤ (Fintype.card n : ℝ) := by
  calc ‖U.trace‖ = ‖∑ i, U i i‖ := by rw [Matrix.trace]; rfl
    _ ≤ ∑ _i : n, (1 : ℝ) := by
        refine (norm_sum_le _ _).trans ?_
        exact Finset.sum_le_sum fun i _ => entry_norm_bound_of_unitary hU i i
    _ = (Fintype.card n : ℝ) := by simp [Finset.card_univ]

/-- **Trace-norm bound for the matrix cosine.**  For a Hermitian complex `n × n` matrix `A`,
the trace of `cos A` has modulus at most `n`. -/
theorem CosTraceNorm3499 {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    ‖(cosMat A).trace‖ ≤ (Fintype.card n : ℝ) := by
  have h1 := norm_trace_le_card_of_mem_unitaryGroup (exp_I_smul_mem_unitary hA)
  have h2 := norm_trace_le_card_of_mem_unitaryGroup (exp_neg_I_smul_mem_unitary hA)
  have htr : (cosMat A).trace
      = (2 : ℂ)⁻¹ * ((exp (Complex.I • A)).trace + (exp (-(Complex.I • A))).trace) := by
    simp [cosMat, Matrix.trace_smul, Matrix.trace_add, smul_eq_mul, mul_add]
  rw [htr, norm_mul]
  have hsum : ‖(exp (Complex.I • A)).trace + (exp (-(Complex.I • A))).trace‖
      ≤ (Fintype.card n : ℝ) + (Fintype.card n : ℝ) := (norm_add_le _ _).trans (by linarith)
  have h2' : ‖(2 : ℂ)⁻¹‖ = (2 : ℝ)⁻¹ := by norm_num
  rw [h2']
  nlinarith [norm_nonneg ((exp (Complex.I • A)).trace + (exp (-(Complex.I • A))).trace)]

/-! ### A sharper, second-order bound -/

/-- Conjugation by a unitary matrix commutes with the matrix exponential. -/
lemma exp_conj_unitary {U : Matrix n n ℂ} (hU : U ∈ Matrix.unitaryGroup n ℂ) (M : Matrix n n ℂ) :
    exp (U * M * star U) = U * exp M * star U := by
  have h1 : U * star U = 1 := Unitary.mul_star_self_of_mem hU
  have h2 : star U * U = 1 := Unitary.star_mul_self_of_mem hU
  let u : (Matrix n n ℂ)ˣ := ⟨U, star U, h1, h2⟩
  have h := Matrix.exp_units_conj u M
  simpa [u, Units.inv_mk] using h

/-- The trace is invariant under conjugation by a unitary matrix. -/
lemma trace_conj_unitary {U : Matrix n n ℂ} (hU : U ∈ Matrix.unitaryGroup n ℂ) (M : Matrix n n ℂ) :
    (U * M * star U).trace = M.trace := by
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, Unitary.star_mul_self_of_mem hU, Matrix.one_mul]

/-- The exponential of a diagonal complex matrix is diagonal, with entrywise `Complex.exp`. -/
lemma exp_diagonal_complex (d : n → ℂ) :
    exp (Matrix.diagonal d) = Matrix.diagonal (fun i => Complex.exp (d i)) := by
  rw [Matrix.exp_diagonal, Pi.exp_def]
  simp [← Complex.exp_eq_exp_ℂ]

/-- The trace of `cos A` of a Hermitian matrix is the sum of the cosines of its eigenvalues. -/
lemma trace_cosMat_eq {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    (cosMat A).trace = ∑ i, (Real.cos (hA.eigenvalues i) : ℂ) := by
  set U : Matrix n n ℂ := (hA.eigenvectorUnitary : Matrix n n ℂ) with hUdef
  have hU : U ∈ Matrix.unitaryGroup n ℂ := hA.eigenvectorUnitary.2
  have hspec : A = U * Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) * star U := by
    have h := hA.spectral_theorem
    rwa [Unitary.conjStarAlgAut_apply] at h
  have key : ∀ z : ℂ, (exp (z • A)).trace = ∑ i, Complex.exp (z * (hA.eigenvalues i : ℂ)) := by
    intro z
    have hsm : z • A = U * Matrix.diagonal (fun i => z * (hA.eigenvalues i : ℂ)) * star U := by
      have hd : (Matrix.diagonal (fun i => z * (hA.eigenvalues i : ℂ)))
          = z • Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) := by
        rw [← Matrix.diagonal_smul]; rfl
      rw [hd, Matrix.mul_smul, Matrix.smul_mul, ← hspec]
    rw [hsm, exp_conj_unitary hU, trace_conj_unitary hU, exp_diagonal_complex,
      Matrix.trace_diagonal]
  have h1 := key Complex.I
  have h2 := key (-Complex.I)
  have hneg : -(Complex.I • A) = (-Complex.I) • A := by module
  rw [cosMat, Matrix.trace_smul, Matrix.trace_add, hneg, h1, h2, ← Finset.sum_add_distrib,
    smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hc : Complex.exp (Complex.I * (hA.eigenvalues i : ℂ))
      + Complex.exp (-Complex.I * (hA.eigenvalues i : ℂ))
      = 2 * Complex.cos (hA.eigenvalues i : ℂ) := by
    rw [Complex.cos]; ring_nf
  rw [hc, ← Complex.ofReal_cos]
  ring

/-- The trace of `A * A` for Hermitian `A` is the sum of the squares of the eigenvalues. -/
lemma trace_mul_self_eq {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    (A * A).trace = ∑ i, ((hA.eigenvalues i : ℂ) ^ 2) := by
  set U : Matrix n n ℂ := (hA.eigenvectorUnitary : Matrix n n ℂ) with hUdef
  have hU : U ∈ Matrix.unitaryGroup n ℂ := hA.eigenvectorUnitary.2
  set D : Matrix n n ℂ := Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) with hDdef
  have hspec : A = U * D * star U := by
    have h := hA.spectral_theorem
    rwa [Unitary.conjStarAlgAut_apply] at h
  have hAA : A * A = U * (D * D) * star U := by
    conv_lhs => rw [hspec]
    have h2 : star U * U = 1 := Unitary.star_mul_self_of_mem hU
    calc U * D * star U * (U * D * star U)
        = U * D * (star U * U) * D * star U := by noncomm_ring
      _ = U * (D * D) * star U := by rw [h2]; noncomm_ring
  rw [hAA, trace_conj_unitary hU, hDdef, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
  simp [Function.comp, sq]

/-- **Second-order trace-norm bound for the matrix cosine.**  For a Hermitian complex `n × n`
matrix `A`, the trace of `cos A` differs from `n` by at most `Tr (A²) / 2`. -/
theorem CosTraceNorm3499_sharp {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    ‖(Fintype.card n : ℂ) - (cosMat A).trace‖ ≤ ((A * A).trace.re) / 2 := by
  set lam : n → ℝ := hA.eigenvalues with hlam
  have htr : (cosMat A).trace = ((∑ i, Real.cos (lam i) : ℝ) : ℂ) := by
    rw [trace_cosMat_eq hA]; push_cast; rfl
  have hAA : (A * A).trace = ((∑ i, (lam i) ^ 2 : ℝ) : ℂ) := by
    rw [trace_mul_self_eq hA]; push_cast; rfl
  have hAAre : (A * A).trace.re = ∑ i, (lam i) ^ 2 := by
    rw [hAA, Complex.ofReal_re]
  have hdiff : (Fintype.card n : ℂ) - (cosMat A).trace
      = (((Fintype.card n : ℝ) - ∑ i, Real.cos (lam i) : ℝ) : ℂ) := by
    rw [htr]; push_cast; ring
  rw [hdiff, hAAre, Complex.norm_real, Real.norm_eq_abs]
  have hcard : (Fintype.card n : ℝ) = ∑ _i : n, (1 : ℝ) := by simp [Finset.card_univ]
  have hupper : (Fintype.card n : ℝ) - ∑ i, Real.cos (lam i) ≤ (∑ i, (lam i) ^ 2) / 2 := by
    rw [hcard, ← Finset.sum_sub_distrib, Finset.sum_div]
    refine Finset.sum_le_sum fun i _ => ?_
    have := Real.one_sub_sq_div_two_le_cos (x := lam i)
    linarith
  have hlower : 0 ≤ (Fintype.card n : ℝ) - ∑ i, Real.cos (lam i) := by
    rw [hcard, ← Finset.sum_sub_distrib]
    exact Finset.sum_nonneg fun i _ => by have := Real.cos_le_one (lam i); linarith
  rw [abs_of_nonneg hlower]
  exact hupper

end Brockian

