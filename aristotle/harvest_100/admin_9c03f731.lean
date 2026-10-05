import Mathlib

/-!
# Uhlmann Fidelity
Category: Frontier Qi
Target: QI.uhlmann_fidelity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix Finset
open scoped MatrixOrder ComplexOrder

namespace QI

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### The dictionary between vectors of `H ⊗ H` and matrices

We model the Hilbert space `H` of a finite quantum system by `EuclideanSpace ℂ n` and the
composite system `H ⊗ H` by `EuclideanSpace ℂ (n × n)`.  A vector of the composite system is
the same thing as a matrix of coefficients. -/

/-- The matrix of coefficients of a vector of `H ⊗ H = EuclideanSpace ℂ (n × n)`. -/
noncomputable def matrixOfVec (ψ : EuclideanSpace ℂ (n × n)) : Matrix n n ℂ :=
  .of fun i j => ψ (i, j)

/-- The vector of `H ⊗ H` with prescribed coefficient matrix. -/
noncomputable def vecOfMatrix (A : Matrix n n ℂ) : EuclideanSpace ℂ (n × n) :=
  WithLp.toLp 2 fun p => A p.1 p.2

/-- The reduced density matrix of the pure state `ψ` of `H ⊗ H`: the partial trace of `|ψ⟩⟨ψ|`
over the second tensor factor. -/
noncomputable def reducedState (ψ : EuclideanSpace ℂ (n × n)) : Matrix n n ℂ :=
  .of fun i i' => ∑ j, ψ (i, j) * (starRingEnd ℂ) (ψ (i', j))

/-- The trace norm `‖M‖₁ = Tr √(Mᴴ M)`. -/
noncomputable def traceNorm (M : Matrix n n ℂ) : ℝ := (CFC.sqrt (Mᴴ * M)).trace.re

/-- The (Uhlmann–Jozsa) fidelity `F(ρ, σ) = ‖√ρ √σ‖₁ = Tr √(√σ ρ √σ)`. -/
noncomputable def fidelity (ρ σ : Matrix n n ℂ) : ℝ := traceNorm (CFC.sqrt ρ * CFC.sqrt σ)

/-- The fidelity is the usual `Tr √(√σ ρ √σ)`. -/
lemma fidelity_eq {ρ σ : Matrix n n ℂ} (hρ : ρ.PosSemidef) :
    fidelity ρ σ = (CFC.sqrt (CFC.sqrt σ * ρ * CFC.sqrt σ)).trace.re := by
  have hRH : (CFC.sqrt ρ)ᴴ = CFC.sqrt ρ := (CFC.sqrt_nonneg ρ).posSemidef.1
  have hSH : (CFC.sqrt σ)ᴴ = CFC.sqrt σ := (CFC.sqrt_nonneg σ).posSemidef.1
  have hRR : CFC.sqrt ρ * CFC.sqrt ρ = ρ := CFC.sqrt_mul_sqrt_self _ hρ.nonneg
  have h : (CFC.sqrt ρ * CFC.sqrt σ)ᴴ * (CFC.sqrt ρ * CFC.sqrt σ)
      = CFC.sqrt σ * ρ * CFC.sqrt σ := by
    rw [Matrix.conjTranspose_mul, hRH, hSH,
      show CFC.sqrt σ * CFC.sqrt ρ * (CFC.sqrt ρ * CFC.sqrt σ)
        = CFC.sqrt σ * (CFC.sqrt ρ * CFC.sqrt ρ) * CFC.sqrt σ from by simp [Matrix.mul_assoc],
      hRR]
  rw [fidelity, traceNorm, h]

/-! ### Elementary lemmas -/

omit [Fintype n] [DecidableEq n] in
@[simp] lemma matrixOfVec_vecOfMatrix (A : Matrix n n ℂ) : matrixOfVec (vecOfMatrix A) = A := rfl

omit [Fintype n] [DecidableEq n] in
@[simp] lemma vecOfMatrix_matrixOfVec (ψ : EuclideanSpace ℂ (n × n)) :
    vecOfMatrix (matrixOfVec ψ) = ψ := rfl

omit [DecidableEq n] in
lemma reducedState_eq (ψ : EuclideanSpace ℂ (n × n)) :
    reducedState ψ = matrixOfVec ψ * (matrixOfVec ψ)ᴴ := by
  ext i i'
  simp [reducedState, matrixOfVec, Matrix.mul_apply, Matrix.conjTranspose_apply]

omit [DecidableEq n] in
lemma inner_eq_trace (ψ φ : EuclideanSpace ℂ (n × n)) :
    (inner ℂ ψ φ : ℂ) = ((matrixOfVec ψ)ᴴ * matrixOfVec φ).trace := by
  simp [PiLp.inner_apply, Matrix.trace, Matrix.mul_apply, matrixOfVec, Matrix.diag,
    Fintype.sum_prod_type, RCLike.inner_apply, mul_comm]
  rw [Finset.sum_comm]

omit [DecidableEq n] in
lemma norm_vecOfMatrix (A : Matrix n n ℂ) : ‖vecOfMatrix A‖ = Real.sqrt ((Aᴴ * A).trace.re) := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  simp only [vecOfMatrix, Matrix.trace, Matrix.mul_apply, Matrix.diag, Fintype.sum_prod_type,
    Matrix.conjTranspose_apply, Complex.re_sum, WithLp.ofLp_toLp]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.sq_norm]
  simp [Complex.normSq_apply]

omit [DecidableEq n] in
/-- Frobenius (Hilbert–Schmidt) Cauchy–Schwarz inequality for the trace pairing. -/
lemma norm_trace_le (A B : Matrix n n ℂ) :
    ‖(Aᴴ * B).trace‖ ≤ Real.sqrt ((Aᴴ * A).trace.re) * Real.sqrt ((Bᴴ * B).trace.re) := by
  have h := norm_inner_le_norm (𝕜 := ℂ) (vecOfMatrix A) (vecOfMatrix B)
  rwa [inner_eq_trace, matrixOfVec_vecOfMatrix, matrixOfVec_vecOfMatrix, norm_vecOfMatrix,
    norm_vecOfMatrix] at h

/-! ### Polar decomposition -/

/-- If the columns of `N` are pairwise orthogonal with norms `s j`, then `N = W * diagonal s`
for a unitary `W`. -/
lemma exists_unitary_mul_diagonal (N : Matrix n n ℂ) (s : n → ℝ)
    (hN : Nᴴ * N = diagonal (fun i => ((s i : ℝ) : ℂ)) * diagonal (fun i => ((s i : ℝ) : ℂ))) :
    ∃ W : Matrix n n ℂ, Wᴴ * W = 1 ∧ W * diagonal (fun i => ((s i : ℝ) : ℂ)) = N := by
  classical
  set col : n → EuclideanSpace ℂ n := fun j => WithLp.toLp 2 (fun i => N i j) with hcoldef
  have hcol : ∀ j k, (inner ℂ (col j) (col k) : ℂ) = if j = k then ((s j : ℂ)) ^ 2 else 0 := by
    intro j k
    have h : (inner ℂ (col j) (col k) : ℂ) = (Nᴴ * N) j k := by
      simp [hcoldef, PiLp.inner_apply, RCLike.inner_apply, Matrix.mul_apply,
        Matrix.conjTranspose_apply, mul_comm]
    rw [h, hN, Matrix.diagonal_mul_diagonal]
    by_cases h' : j = k <;> simp [h', sq]
  set S : Set n := {j | s j ≠ 0} with hSdef
  set u : n → EuclideanSpace ℂ n := fun j => ((s j : ℂ))⁻¹ • col j with hudef
  have horth : Orthonormal ℂ (S.restrict u) := by
    rw [orthonormal_iff_ite]
    rintro ⟨j, hj⟩ ⟨k, hk⟩
    simp only [Set.restrict_apply, hudef, inner_smul_left, inner_smul_right, hcol]
    rw [Complex.conj_inv, Complex.conj_ofReal]
    by_cases h : j = k
    · subst h
      have hne : ((s j : ℂ)) ≠ 0 := by simpa using hj
      field_simp
      simp
    · simp [h, Subtype.ext_iff]
  obtain ⟨b, hb⟩ := horth.exists_orthonormalBasis_extension_of_card_eq
    (by simp [finrank_euclideanSpace] : Module.finrank ℂ (EuclideanSpace ℂ n) = Fintype.card n)
  refine ⟨Matrix.of fun i j => b j i, ?_, ?_⟩
  · ext j k
    have h1 : (inner ℂ (b j) (b k) : ℂ) = if j = k then 1 else 0 :=
      orthonormal_iff_ite.mp b.orthonormal j k
    rw [PiLp.inner_apply] at h1
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.one_apply,
      RCLike.inner_apply] at h1 ⊢
    rw [← h1]
    simp [mul_comm]
  · ext i j
    rw [Matrix.mul_diagonal]
    simp only [Matrix.of_apply]
    by_cases h : s j = 0
    · have h0 : col j = 0 := by
        have hc := hcol j j
        rw [if_pos rfl, h] at hc
        simpa using hc
      have hz : N i j = 0 := by
        have := congrFun (congrArg WithLp.ofLp h0) i
        simpa [hcoldef] using this
      simp [h, hz]
    · rw [hb j h]
      have hne : ((s j : ℂ)) ≠ 0 := by simpa using h
      simp [hudef, hcoldef]
      field_simp

/-- **Polar decomposition** of a square complex matrix: `M = U √(Mᴴ M)` with `U` unitary. -/
theorem exists_unitary_mul_sqrt (M : Matrix n n ℂ) :
    ∃ U : Matrix n n ℂ, Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧ M = U * CFC.sqrt (Mᴴ * M) := by
  have hPSD : (Mᴴ * M).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self M
  set P := CFC.sqrt (Mᴴ * M) with hPdef
  have hPpsd : P.PosSemidef := (CFC.sqrt_nonneg (Mᴴ * M)).posSemidef
  have hPP : P * P = Mᴴ * M := CFC.sqrt_mul_sqrt_self _ hPSD.nonneg
  have hherm : P.IsHermitian := hPpsd.1
  set V : Matrix n n ℂ := (hherm.eigenvectorUnitary : Matrix n n ℂ) with hVdef
  have hV1 : Vᴴ * V = 1 := by
    have h := hherm.eigenvectorUnitary.2
    rw [Matrix.mem_unitaryGroup_iff'] at h
    simpa [hVdef, Matrix.star_eq_conjTranspose] using h
  have hV2 : V * Vᴴ = 1 := by
    have h := hherm.eigenvectorUnitary.2
    rw [Matrix.mem_unitaryGroup_iff] at h
    simpa [hVdef, Matrix.star_eq_conjTranspose] using h
  set D : Matrix n n ℂ := diagonal (fun i => ((hherm.eigenvalues i : ℝ) : ℂ)) with hDdef
  have hspec : P = V * D * Vᴴ := by
    conv_lhs => rw [hherm.spectral_theorem]
    simp [Unitary.conjStarAlgAut_apply, hVdef, hDdef, Matrix.star_eq_conjTranspose,
      Function.comp_def]
  have hN : (M * V)ᴴ * (M * V) = D * D := by
    have h : (M * V)ᴴ * (M * V) = Vᴴ * (P * P) * V := by
      rw [hPP]; simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [h, hspec]
    simp [← Matrix.mul_assoc, hV1]
    simp [Matrix.mul_assoc, hV1]
  obtain ⟨W, hW1, hWD⟩ := exists_unitary_mul_diagonal (M * V) hherm.eigenvalues hN
  have hW2 : W * Wᴴ = 1 := mul_eq_one_comm.mpr hW1
  refine ⟨W * Vᴴ, ?_, ?_, ?_⟩
  · simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [show V * (Wᴴ * (W * Vᴴ)) = V * ((Wᴴ * W) * Vᴴ) by simp [Matrix.mul_assoc], hW1]
    simp [hV2]
  · simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [show W * (Vᴴ * (V * Wᴴ)) = W * ((Vᴴ * V) * Wᴴ) by simp [Matrix.mul_assoc], hV1]
    simp [hW2]
  · rw [hspec]
    have h : W * Vᴴ * (V * D * Vᴴ) = W * ((Vᴴ * V) * D) * Vᴴ := by simp [Matrix.mul_assoc]
    rw [h, hV1, Matrix.one_mul, hWD, Matrix.mul_assoc, hV2, Matrix.mul_one]

/-- Any matrix `A` with `A Aᴴ = ρ` is of the form `√ρ U` with `U` unitary; i.e. all purifications
of `ρ` differ by a unitary on the ancilla. -/
theorem exists_unitary_sqrt_mul {ρ : Matrix n n ℂ} (A : Matrix n n ℂ) (hA : A * Aᴴ = ρ) :
    ∃ U : Matrix n n ℂ, Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧ A = CFC.sqrt ρ * U := by
  obtain ⟨U, hU1, hU2, hU3⟩ := exists_unitary_mul_sqrt Aᴴ
  rw [Matrix.conjTranspose_conjTranspose, hA] at hU3
  refine ⟨Uᴴ, by simpa using hU2, by simpa using hU1, ?_⟩
  have hsqrtH : (CFC.sqrt ρ)ᴴ = CFC.sqrt ρ := (CFC.sqrt_nonneg ρ).posSemidef.1
  have := congrArg Matrix.conjTranspose hU3
  rwa [Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_mul, hsqrtH] at this

/-! ### The variational characterisation of the trace norm -/

omit [DecidableEq n] in
lemma trace_re_of_posSemidef {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    (A.trace : ℂ) = ((A.trace.re : ℝ) : ℂ) ∧ 0 ≤ A.trace.re := by
  have h := hA.trace_nonneg
  rw [Complex.le_def] at h
  exact ⟨by apply Complex.ext <;> simp [← h.2], by simpa using h.1⟩

lemma traceNorm_nonneg (M : Matrix n n ℂ) : 0 ≤ traceNorm M :=
  (trace_re_of_posSemidef (CFC.sqrt_nonneg (Mᴴ * M)).posSemidef).2

/-- `|Tr (M U)| ≤ ‖M‖₁` for unitary `U`. -/
theorem norm_trace_mul_le_traceNorm (M U : Matrix n n ℂ) (hU' : U * Uᴴ = 1) :
    ‖(M * U).trace‖ ≤ traceNorm M := by
  obtain ⟨Z, hZ1, hZ2, hZ3⟩ := exists_unitary_mul_sqrt M
  set P := CFC.sqrt (Mᴴ * M) with hPdef
  have hPpsd : P.PosSemidef := (CFC.sqrt_nonneg (Mᴴ * M)).posSemidef
  set Q := CFC.sqrt P with hQdef
  have hQpsd : Q.PosSemidef := (CFC.sqrt_nonneg P).posSemidef
  have hQQ : Q * Q = P := CFC.sqrt_mul_sqrt_self _ hPpsd.nonneg
  have hQH : Qᴴ = Q := hQpsd.1
  -- the two Hilbert–Schmidt factors
  set X : Matrix n n ℂ := Q * Zᴴ with hXdef
  set Y : Matrix n n ℂ := Q * U with hYdef
  have hXH : Xᴴ = Z * Q := by
    rw [hXdef, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hQH]
  have hXY : Xᴴ * Y = M * U := by
    rw [hXH, hYdef, hZ3, ← hQQ]
    simp [Matrix.mul_assoc]
  have hXX : (Xᴴ * X).trace = P.trace := by
    have h : Xᴴ * X = Z * P * Zᴴ := by
      rw [hXH, hXdef, ← hQQ]; simp [Matrix.mul_assoc]
    rw [h, Matrix.trace_mul_cycle, hZ1, Matrix.one_mul]
  have hYY : (Yᴴ * Y).trace = P.trace := by
    have h : Yᴴ * Y = Uᴴ * P * U := by
      rw [hYdef, Matrix.conjTranspose_mul, hQH, ← hQQ]; simp [Matrix.mul_assoc]
    rw [h, Matrix.trace_mul_cycle, hU', Matrix.one_mul]
  have hnn : 0 ≤ P.trace.re := (trace_re_of_posSemidef hPpsd).2
  have h := norm_trace_le X Y
  rw [hXY, hXX, hYY, Real.mul_self_sqrt hnn] at h
  exact h

/-- The maximum in the variational characterisation of the trace norm is attained. -/
theorem exists_unitary_trace_mul_eq (M : Matrix n n ℂ) :
    ∃ U : Matrix n n ℂ, Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧ (M * U).trace = (traceNorm M : ℂ) := by
  obtain ⟨Z, hZ1, hZ2, hZ3⟩ := exists_unitary_mul_sqrt M
  refine ⟨Zᴴ, by simpa using hZ2, by simpa using hZ1, ?_⟩
  have hPpsd : (CFC.sqrt (Mᴴ * M)).PosSemidef := (CFC.sqrt_nonneg (Mᴴ * M)).posSemidef
  have key : (M * Zᴴ).trace = (CFC.sqrt (Mᴴ * M)).trace := by
    conv_lhs => rw [hZ3]
    rw [Matrix.trace_mul_cycle, hZ1, Matrix.one_mul]
  rw [key]
  exact (trace_re_of_posSemidef hPpsd).1

/-! ### Uhlmann's theorem -/

/-- **Uhlmann's theorem**: the fidelity of two positive semidefinite matrices (density
operators) `ρ` and `σ` is the maximum of the overlap `|⟨ψ, φ⟩|` taken over all purifications
`ψ` of `ρ` and `φ` of `σ` in `H ⊗ H`. -/
theorem uhlmann_fidelity {ρ σ : Matrix n n ℂ} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) :
    IsGreatest {x : ℝ | ∃ ψ φ : EuclideanSpace ℂ (n × n),
        reducedState ψ = ρ ∧ reducedState φ = σ ∧ x = ‖(inner ℂ ψ φ : ℂ)‖}
      (fidelity ρ σ) := by
  set R := CFC.sqrt ρ with hRdef
  set S := CFC.sqrt σ with hSdef
  have hRH : Rᴴ = R := (CFC.sqrt_nonneg ρ).posSemidef.1
  have hSH : Sᴴ = S := (CFC.sqrt_nonneg σ).posSemidef.1
  have hRR : R * R = ρ := CFC.sqrt_mul_sqrt_self _ hρ.nonneg
  have hSS : S * S = σ := CFC.sqrt_mul_sqrt_self _ hσ.nonneg
  constructor
  · -- attainment
    obtain ⟨Z, hZ1, hZ2, hZ3⟩ := exists_unitary_trace_mul_eq (R * S)
    refine ⟨vecOfMatrix R, vecOfMatrix (S * Z), ?_, ?_, ?_⟩
    · rw [reducedState_eq, matrixOfVec_vecOfMatrix, hRH, hRR]
    · rw [reducedState_eq, matrixOfVec_vecOfMatrix, Matrix.conjTranspose_mul, hSH,
        show S * Z * (Zᴴ * S) = S * (Z * Zᴴ) * S by simp [Matrix.mul_assoc], hZ2,
        Matrix.mul_one, hSS]
    · rw [inner_eq_trace, matrixOfVec_vecOfMatrix, matrixOfVec_vecOfMatrix, hRH,
        ← Matrix.mul_assoc, hZ3]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (traceNorm_nonneg _)]
      rfl
  · -- upper bound
    rintro x ⟨ψ, φ, hψ, hφ, rfl⟩
    set A := matrixOfVec ψ with hAdef
    set B := matrixOfVec φ with hBdef
    have hA : A * Aᴴ = ρ := by rw [← reducedState_eq, hψ]
    have hB : B * Bᴴ = σ := by rw [← reducedState_eq, hφ]
    obtain ⟨U, hU1, hU2, hU3⟩ := exists_unitary_sqrt_mul A hA
    obtain ⟨V, hV1, hV2, hV3⟩ := exists_unitary_sqrt_mul B hB
    rw [inner_eq_trace, ← hAdef, ← hBdef, hU3, hV3, Matrix.conjTranspose_mul, hRH]
    have hcyc : (Uᴴ * R * (S * V)).trace = (R * S * (V * Uᴴ)).trace := by
      rw [show Uᴴ * R * (S * V) = Uᴴ * (R * S * V) by simp [Matrix.mul_assoc],
        Matrix.trace_mul_comm]
      simp [Matrix.mul_assoc]
    rw [hcyc]
    refine norm_trace_mul_le_traceNorm _ _ ?_
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      show V * Uᴴ * (U * Vᴴ) = V * (Uᴴ * U) * Vᴴ by simp [Matrix.mul_assoc], hU1,
      Matrix.mul_one, hV2]

end QI

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

