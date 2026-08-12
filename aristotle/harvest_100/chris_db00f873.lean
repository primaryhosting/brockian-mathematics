import Mathlib

/-!
# A trace-norm bound for the matrix cosine

For a Hermitian complex matrix `A` we define the matrix cosine and sine by

  `cos A = (exp (I • A) + exp (-(I • A))) / 2`,  `sin A = (exp (I • A) - exp (-(I • A))) / (2 I)`,

and the trace norm (nuclear norm) of a matrix `M` as the sum of its singular values, i.e.
the sum of the square roots of the eigenvalues of `Mᴴ * M`.

The main result `Brockian.CosTraceNorm4001` states `‖cos A‖₁ ≤ card n`.
-/

namespace Brockian

open Matrix
open scoped ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The trace norm (nuclear norm) of a complex matrix: the sum of its singular values,
i.e. the sum of the square roots of the eigenvalues of `Mᴴ * M`. -/
noncomputable def traceNorm (M : Matrix n n ℂ) : ℝ :=
  ∑ i, Real.sqrt ((Matrix.isHermitian_conjTranspose_mul_self M).eigenvalues i)

/-- The matrix cosine, defined via the matrix exponential. -/
noncomputable def matCos (A : Matrix n n ℂ) : Matrix n n ℂ :=
  (2⁻¹ : ℂ) • (NormedSpace.exp (Complex.I • A) + NormedSpace.exp (-(Complex.I • A)))

/-- The matrix sine, defined via the matrix exponential. -/
noncomputable def matSin (A : Matrix n n ℂ) : Matrix n n ℂ :=
  ((2 * Complex.I)⁻¹ : ℂ) • (NormedSpace.exp (Complex.I • A) - NormedSpace.exp (-(Complex.I • A)))

lemma exp_mul_exp_neg (A : Matrix n n ℂ) :
    NormedSpace.exp (Complex.I • A) * NormedSpace.exp (-(Complex.I • A)) = 1 := by
  have hc : Commute (Complex.I • A) (-(Complex.I • A)) := (Commute.refl _).neg_right
  rw [← Matrix.exp_add_of_commute _ _ hc, add_neg_cancel, NormedSpace.exp_zero]

lemma exp_neg_mul_exp (A : Matrix n n ℂ) :
    NormedSpace.exp (-(Complex.I • A)) * NormedSpace.exp (Complex.I • A) = 1 := by
  have hc : Commute (-(Complex.I • A)) (Complex.I • A) := (Commute.refl _).neg_left
  rw [← Matrix.exp_add_of_commute _ _ hc, neg_add_cancel, NormedSpace.exp_zero]

lemma conjTranspose_exp_I_smul {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    (NormedSpace.exp (Complex.I • A))ᴴ = NormedSpace.exp (-(Complex.I • A)) := by
  rw [← Matrix.exp_conjTranspose]
  congr 1
  rw [Matrix.conjTranspose_smul, hA.eq]
  simp [neg_smul]

lemma conjTranspose_exp_neg_I_smul {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    (NormedSpace.exp (-(Complex.I • A)))ᴴ = NormedSpace.exp (Complex.I • A) := by
  rw [← Matrix.exp_conjTranspose]
  congr 1
  rw [Matrix.conjTranspose_neg, Matrix.conjTranspose_smul, hA.eq]
  simp [neg_smul]

lemma matCos_isHermitian {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    (matCos A).IsHermitian := by
  unfold Matrix.IsHermitian matCos
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, conjTranspose_exp_I_smul hA,
    conjTranspose_exp_neg_I_smul hA]
  rw [add_comm]
  norm_num

lemma matSin_isHermitian {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    (matSin A).IsHermitian := by
  unfold Matrix.IsHermitian matSin
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, conjTranspose_exp_I_smul hA,
    conjTranspose_exp_neg_I_smul hA]
  have hstar : star ((2 * Complex.I)⁻¹ : ℂ) = -((2 * Complex.I)⁻¹ : ℂ) := by
    simp [← Complex.ofReal_ofNat]
  rw [hstar, ← neg_sub (NormedSpace.exp (Complex.I • A)), smul_neg, neg_smul, neg_neg]

lemma matCos_sq_add_matSin_sq (A : Matrix n n ℂ) :
    matCos A * matCos A + matSin A * matSin A = 1 := by
  set E := NormedSpace.exp (Complex.I • A)
  set F := NormedSpace.exp (-(Complex.I • A))
  have h1 : E * F = 1 := exp_mul_exp_neg A
  have h2 : F * E = 1 := exp_neg_mul_exp A
  have hplus : (E + F) * (E + F) = (E * E + F * F) + (E * F + F * E) := by noncomm_ring
  have hminus : (E - F) * (E - F) = (E * E + F * F) - (E * F + F * E) := by noncomm_ring
  have hexp : (E + F) * (E + F) = (E * E + F * F) + (2 : ℂ) • (1 : Matrix n n ℂ) := by
    rw [hplus, h1, h2]; module
  have hexm : (E - F) * (E - F) = (E * E + F * F) - (2 : ℂ) • (1 : Matrix n n ℂ) := by
    rw [hminus, h1, h2]; module
  have h4 : (2 * Complex.I) * (2 * Complex.I) = -4 := by
    linear_combination (4 : ℂ) * Complex.I_mul_I
  have hc : ((2 * Complex.I)⁻¹ * (2 * Complex.I)⁻¹ : ℂ) = -(4⁻¹ : ℂ) := by
    rw [← mul_inv, h4]; norm_num
  rw [matCos, matSin, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, hexp, hexm, hc]
  module

/-- The Hilbert–Schmidt bound: `tr ((cos A)ᴴ (cos A)) ≤ card n`. -/
lemma trace_cos_sq_le {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    (Matrix.trace ((matCos A)ᴴ * matCos A)).re ≤ (Fintype.card n : ℝ) := by
  have hC : (matCos A)ᴴ = matCos A := (matCos_isHermitian hA).eq
  have hS : (matSin A)ᴴ = matSin A := (matSin_isHermitian hA).eq
  have hsplit : matCos A * matCos A = 1 - matSin A * matSin A := by
    have := matCos_sq_add_matSin_sq A
    linear_combination (norm := module) this
  have hpsd : (matSin A * matSin A).PosSemidef := by
    have := Matrix.posSemidef_conjTranspose_mul_self (matSin A)
    rwa [hS] at this
  have hnn : (0 : ℂ) ≤ Matrix.trace (matSin A * matSin A) := hpsd.trace_nonneg
  have hre : 0 ≤ (Matrix.trace (matSin A * matSin A)).re := (Complex.nonneg_iff.mp hnn).1
  rw [hC, hsplit, Matrix.trace_sub, Matrix.trace_one]
  simp only [Complex.sub_re, Complex.natCast_re]
  linarith

lemma sum_eigenvalues_eq_trace_re {M : Matrix n n ℂ} (hM : M.IsHermitian) :
    ∑ i, hM.eigenvalues i = (Matrix.trace M).re := by
  rw [hM.trace_eq_sum_eigenvalues]
  rw [Complex.re_sum]
  simp

/-- **A trace-norm bound for the matrix cosine.**  For a Hermitian matrix `A`, the trace norm
(sum of singular values) of `cos A` is at most the dimension. -/
theorem CosTraceNorm4001 {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    traceNorm (matCos A) ≤ (Fintype.card n : ℝ) := by
  set C := matCos A
  set hH := Matrix.isHermitian_conjTranspose_mul_self C
  set mu : n → ℝ := hH.eigenvalues with hmu
  have hmu_nonneg : ∀ i, 0 ≤ mu i :=
    fun i => (Matrix.posSemidef_conjTranspose_mul_self C).eigenvalues_nonneg i
  have hsum : ∑ i, mu i ≤ (Fintype.card n : ℝ) := by
    rw [hmu, sum_eigenvalues_eq_trace_re hH]
    exact trace_cos_sq_le hA
  have hsq : (traceNorm C) ^ 2 ≤ (Fintype.card n : ℝ) * ∑ i, mu i := by
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset n))
      (f := fun i => Real.sqrt (mu i))
    simpa [traceNorm, Real.sq_sqrt, hmu_nonneg, Finset.card_univ,
      Real.sq_sqrt (hmu_nonneg _)] using this
  have hcard : (0 : ℝ) ≤ (Fintype.card n : ℝ) := Nat.cast_nonneg _
  have h2 : (traceNorm C) ^ 2 ≤ (Fintype.card n : ℝ) ^ 2 := by
    calc (traceNorm C) ^ 2 ≤ (Fintype.card n : ℝ) * ∑ i, mu i := hsq
      _ ≤ (Fintype.card n : ℝ) * (Fintype.card n : ℝ) := mul_le_mul_of_nonneg_left hsum hcard
      _ = (Fintype.card n : ℝ) ^ 2 := by ring
  have hnonneg : 0 ≤ traceNorm C :=
    Finset.sum_nonneg fun i _ => Real.sqrt_nonneg _
  nlinarith [h2, hnonneg, hcard]

/-- The trace norm of the identity matrix is the dimension. -/
lemma traceNorm_one : traceNorm (1 : Matrix n n ℂ) = (Fintype.card n : ℝ) := by
  have h : ∀ i : n,
      (Matrix.isHermitian_conjTranspose_mul_self (1 : Matrix n n ℂ)).eigenvalues i = 1 := by
    intro i
    haveI : Nonempty n := ⟨i⟩
    have hmem :=
      (Matrix.isHermitian_conjTranspose_mul_self (1 : Matrix n n ℂ)).eigenvalues_mem_spectrum_real i
    have hspec : spectrum ℝ ((1 : Matrix n n ℂ)ᴴ * 1) = {1} := by
      rw [Matrix.conjTranspose_one, Matrix.one_mul]; exact spectrum.one_eq
    rw [hspec] at hmem
    simpa using hmem
  have h' : ∀ i : n,
      Real.sqrt ((Matrix.isHermitian_conjTranspose_mul_self (1 : Matrix n n ℂ)).eigenvalues i)
        = 1 := fun i => by rw [h i, Real.sqrt_one]
  rw [traceNorm, Finset.sum_congr rfl (fun i _ => h' i)]
  simp

lemma matCos_zero : matCos (0 : Matrix n n ℂ) = 1 := by
  rw [matCos]
  simp only [smul_zero, neg_zero, NormedSpace.exp_zero]
  module

/-- The bound in `CosTraceNorm4001` is sharp: it is attained at `A = 0`. -/
theorem CosTraceNorm4001_sharp :
    traceNorm (matCos (0 : Matrix n n ℂ)) = (Fintype.card n : ℝ) := by
  rw [matCos_zero, traceNorm_one]

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

