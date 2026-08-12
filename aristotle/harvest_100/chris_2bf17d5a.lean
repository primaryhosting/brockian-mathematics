/-
# Uhlmann Fidelity
Category: Frontier Qi
Target: QI.uhlmann_fidelity
Statement: Fidelity equals the maximal overlap over purifications (Uhlmann's theorem).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Uhlmann Fidelity
Category: Frontier Qi
Target: QI.uhlmann_fidelity
Statement: Fidelity equals the maximal overlap over purifications (Uhlmann's theorem).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix
open scoped MatrixOrder ComplexOrder

namespace QI

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## Basic notions

We work with a finite dimensional quantum system with Hilbert space `EuclideanSpace ℂ n`.
States are described by positive semidefinite matrices, and a purification of a state `ρ`
on the system is a vector of the composite system `EuclideanSpace ℂ (n × m)` (the tensor
product of the system with an ancilla) whose reduced density matrix (the partial trace over
the ancilla) is `ρ`.
-/

/-- The partial trace over the second (ancilla) tensor factor. -/
noncomputable def ptraceRight {m : Type*} [Fintype m]
    (X : Matrix (n × m) (n × m) ℂ) : Matrix n n ℂ :=
  Matrix.of fun i k => ∑ j, X (i, j) (k, j)

/-- The (rank one) density matrix `|v⟩⟨v|` associated to a vector `v`. -/
noncomputable def pureDensity {N : Type*} [Fintype N] (v : EuclideanSpace ℂ N) : Matrix N N ℂ :=
  Matrix.of fun p q => v.ofLp p * (starRingEnd ℂ) (v.ofLp q)

/-- `v` is a purification of the state `ρ`: the partial trace over the ancilla of the pure
state `|v⟩⟨v|` is `ρ`. -/
def IsPurification {m : Type*} [Fintype m] (v : EuclideanSpace ℂ (n × m))
    (ρ : Matrix n n ℂ) : Prop :=
  ptraceRight (pureDensity v) = ρ

/-- The fidelity `F(ρ, σ) = tr √(√ρ σ √ρ)` of two states. -/
noncomputable def fidelity (ρ σ : Matrix n n ℂ) : ℝ :=
  (Matrix.trace (CFC.sqrt (CFC.sqrt ρ * σ * CFC.sqrt ρ))).re

/-- Sanity check: the fidelity of a state with itself is its trace (`1` for a density
matrix). -/
theorem fidelity_self {ρ : Matrix n n ℂ} (hρ : ρ.PosSemidef) :
    fidelity ρ ρ = (Matrix.trace ρ).re := by
  have hs : CFC.sqrt ρ * CFC.sqrt ρ = ρ := CFC.sqrt_mul_sqrt_self ρ hρ.nonneg
  have h1 : CFC.sqrt ρ * ρ * CFC.sqrt ρ
      = (CFC.sqrt ρ * CFC.sqrt ρ) * (CFC.sqrt ρ * CFC.sqrt ρ) := by
    nth_rewrite 2 [← hs]
    simp only [Matrix.mul_assoc]
  rw [fidelity, h1, hs, ← sq, CFC.sqrt_sq ρ hρ.nonneg]

/-! ## The matrix–vector dictionary

A vector of `EuclideanSpace ℂ (n × m)`, i.e. of the system tensored with an ancilla, is the
same thing as an `n × m` matrix.  Under this dictionary the partial trace of `|v⟩⟨v|`
becomes `A Aᴴ` and the inner product becomes the trace pairing.
-/

/-- The vector of `EuclideanSpace ℂ (n × m)` associated to a matrix. -/
noncomputable def matToVec {m : Type*} [Fintype m] (A : Matrix n m ℂ) :
    EuclideanSpace ℂ (n × m) :=
  WithLp.toLp 2 (fun p => A p.1 p.2)

/-- The matrix associated to a vector of `EuclideanSpace ℂ (n × m)`. -/
noncomputable def vecToMat {m : Type*} [Fintype m] (v : EuclideanSpace ℂ (n × m)) :
    Matrix n m ℂ :=
  Matrix.of fun i j => v.ofLp (i, j)

omit [Fintype n] [DecidableEq n] in
@[simp] theorem matToVec_vecToMat {m : Type*} [Fintype m] (v : EuclideanSpace ℂ (n × m)) :
    matToVec (vecToMat v) = v := by
  ext p
  simp [matToVec, vecToMat]

omit [DecidableEq n] in
theorem inner_matToVec {m : Type*} [Fintype m] (A B : Matrix n m ℂ) :
    (inner ℂ (matToVec A) (matToVec B) : ℂ) = Matrix.trace (Aᴴ * B) := by
  rw [PiLp.inner_apply]
  simp only [matToVec, WithLp.ofLp_toLp, RCLike.inner_apply, Matrix.trace, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.diag_apply, ← Finset.sum_product']
  exact Fintype.sum_equiv (Equiv.prodComm n m) _ _ (fun p => by simp [mul_comm])

omit [DecidableEq n] in
theorem norm_matToVec {m : Type*} [Fintype m] (A : Matrix n m ℂ) :
    ‖matToVec A‖ = Real.sqrt (Matrix.trace (Aᴴ * A)).re := by
  have h : ‖matToVec A‖ ^ 2 = (Matrix.trace (Aᴴ * A)).re := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
    simp only [matToVec, Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.diag_apply, ← Finset.sum_product', Complex.re_sum, Complex.mul_re,
      WithLp.ofLp_toLp, Complex.star_def, Complex.conj_re, Complex.conj_im]
    refine Fintype.sum_equiv (Equiv.prodComm n m) _ _ (fun p => ?_)
    simp only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  rw [← h, Real.sqrt_sq (norm_nonneg _)]

omit [DecidableEq n] in
/-- The reduced density matrix of the purification associated to `A` is `A Aᴴ`. -/
theorem ptraceRight_pureDensity_matToVec {m : Type*} [Fintype m] (A : Matrix n m ℂ) :
    ptraceRight (pureDensity (matToVec A)) = A * Aᴴ := by
  ext i k
  simp [ptraceRight, pureDensity, matToVec, Matrix.mul_apply, Matrix.conjTranspose_apply]

omit [DecidableEq n] in
/-- `matToVec A` purifies `ρ` exactly when `A Aᴴ = ρ`. -/
theorem isPurification_matToVec_iff {m : Type*} [Fintype m] (A : Matrix n m ℂ)
    (ρ : Matrix n n ℂ) :
    IsPurification (matToVec A) ρ ↔ A * Aᴴ = ρ := by
  rw [IsPurification, ptraceRight_pureDensity_matToVec]

/-! ## Auxiliary results -/

omit [DecidableEq n] in
/-- Hilbert–Schmidt (Frobenius) Cauchy–Schwarz inequality for the trace pairing. -/
theorem norm_trace_conjTranspose_mul_le (X Y : Matrix n n ℂ) :
    ‖Matrix.trace (Xᴴ * Y)‖ ≤
      Real.sqrt (Matrix.trace (Xᴴ * X)).re * Real.sqrt (Matrix.trace (Yᴴ * Y)).re := by
  rw [← inner_matToVec, ← norm_matToVec, ← norm_matToVec]
  exact norm_inner_le_norm (matToVec X) (matToVec Y)

/-- `⟪Ax, Ax⟫ = ⟪x, AᴴA x⟫`. -/
theorem inner_toEuclideanLin_self {m : Type*} [Fintype m] [DecidableEq m] (A : Matrix n m ℂ)
    (x : EuclideanSpace ℂ m) :
    (inner ℂ (Matrix.toEuclideanLin A x) (Matrix.toEuclideanLin A x) : ℂ)
      = inner ℂ x (Matrix.toEuclideanLin (Aᴴ * A) x) := by
  have h : Matrix.toEuclideanLin (Aᴴ * A)
      = (LinearMap.adjoint (Matrix.toEuclideanLin A)).comp (Matrix.toEuclideanLin A) := by
    rw [Matrix.toLpLin_mul, Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  rw [h]
  simp [LinearMap.adjoint_inner_right]

/-- Polar decomposition: every square complex matrix `M` factors as a unitary times the
positive semidefinite matrix `√(Mᴴ M)`. -/
theorem exists_unitary_mul_sqrt (M : Matrix n n ℂ) :
    ∃ W ∈ unitaryGroup n ℂ, M = W * CFC.sqrt (Mᴴ * M) := by
  set P := CFC.sqrt (Mᴴ * M) with hPdef
  have hPh : Pᴴ = P := (CFC.sqrt_nonneg (Mᴴ * M)).posSemidef.1
  have hPP : Pᴴ * P = Mᴴ * M := by
    rw [hPh]
    exact CFC.sqrt_mul_sqrt_self _ (Matrix.posSemidef_conjTranspose_mul_self M).nonneg
  set mM := Matrix.toEuclideanLin M with hmM
  set mP := Matrix.toEuclideanLin P with hmP
  have hnorm : ∀ x : EuclideanSpace ℂ n, ‖mM x‖ = ‖mP x‖ := by
    intro x
    have key : (inner ℂ (mM x) (mM x) : ℂ) = inner ℂ (mP x) (mP x) := by
      rw [inner_toEuclideanLin_self, inner_toEuclideanLin_self, hPP]
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ), key]
  have hker : LinearMap.ker mP ≤ LinearMap.ker mM := by
    intro x hx
    simp only [LinearMap.mem_ker] at hx ⊢
    have hx' := hnorm x
    rw [hx, norm_zero] at hx'
    exact norm_eq_zero.mp hx'
  set L₀ : (LinearMap.range mP) →ₗ[ℂ] EuclideanSpace ℂ n :=
    ((LinearMap.ker mP).liftQ mM hker).comp (mP.quotKerEquivRange.symm : _ →ₗ[ℂ] _) with hL₀def
  have hL₀ : ∀ (x : EuclideanSpace ℂ n) (h : mP x ∈ LinearMap.range mP), L₀ ⟨mP x, h⟩ = mM x := by
    intro x h
    rw [hL₀def]
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply, Submodule.liftQ_apply]
  have hiso : ∀ y : (LinearMap.range mP), ‖L₀ y‖ = ‖(y : EuclideanSpace ℂ n)‖ := by
    rintro ⟨y, x, rfl⟩
    rw [hL₀ x]
    simpa using hnorm x
  set L : (LinearMap.range mP) →ₗᵢ[ℂ] EuclideanSpace ℂ n := ⟨L₀, hiso⟩ with hLdef
  set W' := L.extend with hW'
  have hWP : ∀ x : EuclideanSpace ℂ n, W' (mP x) = mM x := by
    intro x
    have h1 : W' ((⟨mP x, ⟨x, rfl⟩⟩ : LinearMap.range mP) : EuclideanSpace ℂ n)
        = L ⟨mP x, ⟨x, rfl⟩⟩ := L.extend_apply _
    simpa [hLdef, hL₀ x] using h1
  set W := Matrix.toEuclideanLin.symm W'.toLinearMap with hWdef
  have hWlin : Matrix.toEuclideanLin W = W'.toLinearMap := by
    rw [hWdef, LinearEquiv.apply_symm_apply]
  refine ⟨W, ?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff']
    apply Matrix.toEuclideanLin.injective
    have h2 : Matrix.toEuclideanLin (star W * W)
        = (LinearMap.adjoint (Matrix.toEuclideanLin W)).comp (Matrix.toEuclideanLin W) := by
      rw [show star W = Wᴴ from rfl, Matrix.toLpLin_mul,
        Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    rw [h2]
    refine LinearMap.ext fun x => ?_
    refine ext_inner_left ℂ fun y => ?_
    rw [LinearMap.comp_apply, LinearMap.adjoint_inner_right, hWlin]
    simp
  · apply Matrix.toEuclideanLin.injective
    refine LinearMap.ext fun x => ?_
    rw [Matrix.toLpLin_mul]
    simp only [LinearMap.comp_apply]
    rw [show (Matrix.toEuclideanLin P) x = mP x from rfl, hWlin]
    exact (hWP x).symm

/-- If `A Aᴴ = B Bᴴ` then `A = B U` for some unitary `U`. -/
theorem exists_unitary_of_mul_conjTranspose_eq {A B : Matrix n n ℂ} (h : A * Aᴴ = B * Bᴴ) :
    ∃ U ∈ unitaryGroup n ℂ, A = B * U := by
  obtain ⟨W₁, hW₁, hA⟩ := exists_unitary_mul_sqrt Aᴴ
  obtain ⟨W₂, hW₂, hB⟩ := exists_unitary_mul_sqrt Bᴴ
  rw [Matrix.conjTranspose_conjTranspose] at hA hB
  rw [← h] at hB
  set S := CFC.sqrt (A * Aᴴ) with hSdef
  have hSh : Sᴴ = S := (CFC.sqrt_nonneg (A * Aᴴ)).posSemidef.1
  have hA' : A = S * W₁ᴴ := by
    have := congrArg Matrix.conjTranspose hA
    simpa [Matrix.conjTranspose_mul, hSh] using this
  have hB' : B = S * W₂ᴴ := by
    have := congrArg Matrix.conjTranspose hB
    simpa [Matrix.conjTranspose_mul, hSh] using this
  have hW₂star : (W₂ᴴ : Matrix n n ℂ) * W₂ = 1 := Matrix.mem_unitaryGroup_iff'.mp hW₂
  refine ⟨W₂ * W₁ᴴ, Submonoid.mul_mem _ hW₂ (Unitary.star_mem hW₁), ?_⟩
  rw [hB', hA']
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc W₂ᴴ W₂, hW₂star, Matrix.one_mul]

/-- Duality bound: `|tr (M U)| ≤ tr √(Mᴴ M)` for every unitary `U`. -/
theorem norm_trace_mul_unitary_le (M : Matrix n n ℂ) {U : Matrix n n ℂ}
    (hU : U ∈ unitaryGroup n ℂ) :
    ‖Matrix.trace (M * U)‖ ≤ (Matrix.trace (CFC.sqrt (Mᴴ * M))).re := by
  obtain ⟨W, hW, hM⟩ := exists_unitary_mul_sqrt M
  set P := CFC.sqrt (Mᴴ * M) with hPdef
  have hPpsd : P.PosSemidef := (CFC.sqrt_nonneg (Mᴴ * M)).posSemidef
  set Q := CFC.sqrt P with hQdef
  have hQh : Qᴴ = Q := (CFC.sqrt_nonneg P).posSemidef.1
  have hQQ : Q * Q = P := CFC.sqrt_mul_sqrt_self _ hPpsd.nonneg
  have hUstar' : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hU
  have hWstar' : W * Wᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hW
  have htr : Matrix.trace (M * U) = Matrix.trace (Qᴴ * (Q * U * W)) := by
    rw [hM, hQh]
    rw [show W * P * U = W * (Q * (Q * U)) by rw [← hQQ]; noncomm_ring]
    rw [Matrix.trace_mul_comm W (Q * (Q * U))]
    congr 1
    noncomm_ring
  have h1 : Matrix.trace (Qᴴ * Q) = Matrix.trace P := by rw [hQh, hQQ]
  have h2 : Matrix.trace ((Q * U * W)ᴴ * (Q * U * W)) = Matrix.trace P := by
    have e1 : (Q * U * W)ᴴ * (Q * U * W) = Wᴴ * (Uᴴ * P * U * W) := by
      simp only [Matrix.conjTranspose_mul, hQh]
      rw [← hQQ]; noncomm_ring
    have e2 : Matrix.trace (Wᴴ * (Uᴴ * P * U * W)) = Matrix.trace ((Uᴴ * P * U) * (W * Wᴴ)) := by
      rw [Matrix.trace_mul_comm]
      congr 1
      noncomm_ring
    rw [e1, e2, hWstar', Matrix.mul_one, Matrix.trace_mul_comm (Uᴴ * P) U,
      ← Matrix.mul_assoc, hUstar', Matrix.one_mul]
  have hnn : (0:ℝ) ≤ (Matrix.trace P).re := by
    have h := hPpsd.trace_nonneg
    simpa using (Complex.le_def.mp h).1
  calc ‖Matrix.trace (M * U)‖
      = ‖Matrix.trace (Qᴴ * (Q * U * W))‖ := by rw [htr]
    _ ≤ Real.sqrt (Matrix.trace (Qᴴ * Q)).re *
          Real.sqrt (Matrix.trace ((Q * U * W)ᴴ * (Q * U * W))).re :=
        norm_trace_conjTranspose_mul_le _ _
    _ = (Matrix.trace P).re := by
        rw [h1, h2]; exact Real.mul_self_sqrt hnn

/-- The duality bound is attained. -/
theorem exists_unitary_trace_mul_eq (M : Matrix n n ℂ) :
    ∃ U ∈ unitaryGroup n ℂ,
      Matrix.trace (M * U) = (Matrix.trace (CFC.sqrt (Mᴴ * M)) : ℂ) := by
  obtain ⟨W, hW, hM⟩ := exists_unitary_mul_sqrt M
  set P := CFC.sqrt (Mᴴ * M) with hPdef
  have hWstar : Wᴴ * W = 1 := Matrix.mem_unitaryGroup_iff'.mp hW
  refine ⟨Wᴴ, Unitary.star_mem hW, ?_⟩
  conv_lhs => rw [hM]
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hWstar, Matrix.one_mul]

/-! ## Uhlmann's theorem, matrix form -/

/-- Uhlmann's theorem in matrix language: writing purifications of `ρ` as square matrices `A`
with `A Aᴴ = ρ`, the fidelity is the maximum of `|tr (Aᴴ B)|`. -/
theorem uhlmann_matrix {ρ σ : Matrix n n ℂ} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) :
    IsGreatest {t : ℝ | ∃ A B : Matrix n n ℂ,
      A * Aᴴ = ρ ∧ B * Bᴴ = σ ∧ t = ‖Matrix.trace (Aᴴ * B)‖} (fidelity ρ σ) := by
  set R := CFC.sqrt ρ with hRdef
  set S := CFC.sqrt σ with hSdef
  have hRh : Rᴴ = R := (CFC.sqrt_nonneg ρ).posSemidef.1
  have hSh : Sᴴ = S := (CFC.sqrt_nonneg σ).posSemidef.1
  have hRR : R * R = ρ := CFC.sqrt_mul_sqrt_self _ hρ.nonneg
  have hSS : S * S = σ := CFC.sqrt_mul_sqrt_self _ hσ.nonneg
  set M := S * R with hMdef
  have hMM : Mᴴ * M = R * σ * R := by
    rw [hMdef, Matrix.conjTranspose_mul, hRh, hSh, ← hSS]
    noncomm_ring
  have hfid : fidelity ρ σ = (Matrix.trace (CFC.sqrt (Mᴴ * M))).re := by
    rw [fidelity, hMM, ← hRdef]
  constructor
  · -- attainment
    obtain ⟨U, hU, hUeq⟩ := exists_unitary_trace_mul_eq M
    have hUstar : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
    have hUstar' : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hU
    refine ⟨R * U, S, ?_, ?_, ?_⟩
    · rw [Matrix.conjTranspose_mul, hRh, ← Matrix.mul_assoc, Matrix.mul_assoc R U,
        hUstar', Matrix.mul_one, hRR]
    · rw [hSh, hSS]
    · have hconj : Matrix.trace (((R * U)ᴴ * S)ᴴ) = Matrix.trace (M * U) := by
        rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hSh, hMdef,
          Matrix.mul_assoc]
      have hnorm : ‖Matrix.trace ((R * U)ᴴ * S)‖ = ‖Matrix.trace (M * U)‖ := by
        rw [← hconj, Matrix.trace_conjTranspose, norm_star]
      rw [hnorm, hUeq, hfid]
      have hpsd : (CFC.sqrt (Mᴴ * M)).PosSemidef := (CFC.sqrt_nonneg _).posSemidef
      have hle : (0 : ℂ) ≤ Matrix.trace (CFC.sqrt (Mᴴ * M)) := hpsd.trace_nonneg
      obtain ⟨h1, h2⟩ := Complex.le_def.mp hle
      rw [Complex.norm_def, Complex.normSq_apply]
      simp only [Complex.zero_re, Complex.zero_im] at h1 h2
      rw [← h2]
      simp [Real.sqrt_mul_self, h1]
  · -- upper bound
    rintro t ⟨A, B, hA, hB, rfl⟩
    obtain ⟨U, hU, hAU⟩ : ∃ U ∈ unitaryGroup n ℂ, A = R * U := by
      refine exists_unitary_of_mul_conjTranspose_eq ?_
      rw [hA, hRh, hRR]
    obtain ⟨V, hV, hBV⟩ : ∃ V ∈ unitaryGroup n ℂ, B = S * V := by
      refine exists_unitary_of_mul_conjTranspose_eq ?_
      rw [hB, hSh, hSS]
    have hVstar : Vᴴ * V = 1 := Matrix.mem_unitaryGroup_iff'.mp hV
    have hVstar' : V * Vᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hV
    have hUV : (U * Vᴴ) ∈ unitaryGroup n ℂ := Submonoid.mul_mem _ hU (Unitary.star_mem hV)
    have e : (Aᴴ * B)ᴴ = Vᴴ * (S * R * U) := by
      rw [hAU, hBV]
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hRh, hSh]
      noncomm_ring
    have hconj : Matrix.trace ((Aᴴ * B)ᴴ) = Matrix.trace (M * (U * Vᴴ)) := by
      rw [e, Matrix.trace_mul_comm, hMdef, Matrix.mul_assoc]
    have hnorm : ‖Matrix.trace (Aᴴ * B)‖ = ‖Matrix.trace (M * (U * Vᴴ))‖ := by
      rw [← hconj, Matrix.trace_conjTranspose, norm_star]
    rw [hnorm, hfid]
    exact norm_trace_mul_unitary_le M hUV

/-! ## Uhlmann's theorem -/

/-- **Uhlmann's theorem**: the fidelity `F(ρ, σ) = tr √(√ρ σ √ρ)` of two states equals the
maximal overlap `|⟪v, w⟫|` between purifications `v` of `ρ` and `w` of `σ` (with an ancilla
of the same dimension as the system). -/
theorem uhlmann_fidelity {ρ σ : Matrix n n ℂ} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) :
    IsGreatest {t : ℝ | ∃ v w : EuclideanSpace ℂ (n × n),
      IsPurification v ρ ∧ IsPurification w σ ∧ t = ‖(inner ℂ v w : ℂ)‖} (fidelity ρ σ) := by
  have hset : {t : ℝ | ∃ v w : EuclideanSpace ℂ (n × n),
      IsPurification v ρ ∧ IsPurification w σ ∧ t = ‖(inner ℂ v w : ℂ)‖}
      = {t : ℝ | ∃ A B : Matrix n n ℂ,
        A * Aᴴ = ρ ∧ B * Bᴴ = σ ∧ t = ‖Matrix.trace (Aᴴ * B)‖} := by
    ext t
    constructor
    · rintro ⟨v, w, hv, hw, rfl⟩
      refine ⟨vecToMat v, vecToMat w, ?_, ?_, ?_⟩
      · rw [← isPurification_matToVec_iff, matToVec_vecToMat]; exact hv
      · rw [← isPurification_matToVec_iff, matToVec_vecToMat]; exact hw
      · rw [← inner_matToVec, matToVec_vecToMat, matToVec_vecToMat]
    · rintro ⟨A, B, hA, hB, rfl⟩
      refine ⟨matToVec A, matToVec B, ?_, ?_, ?_⟩
      · rw [isPurification_matToVec_iff]; exact hA
      · rw [isPurification_matToVec_iff]; exact hB
      · rw [inner_matToVec]
  rw [hset]
  exact uhlmann_matrix hρ hσ

end QI

import RequestProject.Uhlmann

/-!
# Uhlmann fidelity: purifications with an arbitrary ancilla

`RequestProject.Uhlmann` proves Uhlmann's theorem with an ancilla of the same dimension as
the system.  Here we complement it by showing that the fidelity bounds the overlap of *any*
pair of purifications, whatever the dimension of the ancilla.
-/

open Matrix
open scoped MatrixOrder ComplexOrder

namespace QI

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- If `A Aᴴ = R Rᴴ`, then `A = R V` for a contraction `V` whose adjoint is a contraction
as well.  (This is the rectangular analogue of `QI.exists_unitary_of_mul_conjTranspose_eq`.) -/
theorem exists_contraction_of_mul_conjTranspose_eq {A : Matrix n m ℂ} {R : Matrix n n ℂ}
    (h : A * Aᴴ = R * Rᴴ) :
    ∃ V : Matrix n m ℂ, A = R * V ∧
      (∀ z : EuclideanSpace ℂ m, ‖Matrix.toEuclideanLin V z‖ ≤ ‖z‖) ∧
      (∀ y : EuclideanSpace ℂ n, ‖Matrix.toEuclideanLin Vᴴ y‖ ≤ ‖y‖) := by
  set mA := Matrix.toEuclideanLin Aᴴ with hmA
  set mR := Matrix.toEuclideanLin Rᴴ with hmR
  have hnorm : ∀ x : EuclideanSpace ℂ n, ‖mA x‖ = ‖mR x‖ := by
    intro x
    have key : (inner ℂ (mA x) (mA x) : ℂ) = inner ℂ (mR x) (mR x) := by
      rw [hmA, hmR, inner_toEuclideanLin_self, inner_toEuclideanLin_self]
      simp only [Matrix.conjTranspose_conjTranspose]
      rw [h]
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ), key]
  have hker : LinearMap.ker mR ≤ LinearMap.ker mA := by
    intro x hx
    simp only [LinearMap.mem_ker] at hx ⊢
    have hx' := hnorm x
    rw [hx, norm_zero] at hx'
    exact norm_eq_zero.mp hx'
  set L₀ : (LinearMap.range mR) →ₗ[ℂ] EuclideanSpace ℂ m :=
    ((LinearMap.ker mR).liftQ mA hker).comp (mR.quotKerEquivRange.symm : _ →ₗ[ℂ] _) with hL₀def
  have hL₀ : ∀ (x : EuclideanSpace ℂ n) (hx : mR x ∈ LinearMap.range mR),
      L₀ ⟨mR x, hx⟩ = mA x := by
    intro x hx
    rw [hL₀def]
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply, Submodule.liftQ_apply]
  have hiso : ∀ y : (LinearMap.range mR), ‖L₀ y‖ = ‖(y : EuclideanSpace ℂ n)‖ := by
    rintro ⟨y, x, rfl⟩
    rw [hL₀ x]
    simpa using hnorm x
  set T : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ m :=
    L₀.comp (LinearMap.range mR).orthogonalProjection.toLinearMap with hTdef
  have hT : ∀ x : EuclideanSpace ℂ n, T (mR x) = mA x := by
    intro x
    have hmem : mR x ∈ LinearMap.range mR := ⟨x, rfl⟩
    have hproj : (LinearMap.range mR).orthogonalProjection (mR x) = ⟨mR x, hmem⟩ :=
      Submodule.orthogonalProjection_mem_subspace_eq_self ⟨mR x, hmem⟩
    rw [hTdef]
    simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, hproj]
    exact hL₀ x hmem
  have hTnorm : ∀ y : EuclideanSpace ℂ n, ‖T y‖ ≤ ‖y‖ := by
    intro y
    rw [hTdef]
    simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
    rw [hiso]
    exact (LinearMap.range mR).norm_orthogonalProjection_apply_le y
  set Vc := Matrix.toEuclideanLin.symm T with hVcdef
  have hVclin : Matrix.toEuclideanLin Vc = T := by rw [hVcdef, LinearEquiv.apply_symm_apply]
  have hadj : Matrix.toEuclideanLin (Vcᴴ) = LinearMap.adjoint T := by
    rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint, hVclin]
  refine ⟨Vcᴴ, ?_, ?_, ?_⟩
  · have hAeq : Aᴴ = Vc * Rᴴ := by
      apply Matrix.toEuclideanLin.injective
      refine LinearMap.ext fun x => ?_
      rw [Matrix.toLpLin_mul]
      simp only [LinearMap.comp_apply]
      rw [hVclin]
      exact (hT x).symm
    have hc := congrArg Matrix.conjTranspose hAeq
    simpa [Matrix.conjTranspose_mul] using hc
  · intro u
    rw [hadj]
    set a := LinearMap.adjoint T u with hadef
    have h1 : ‖a‖ ^ 2 = RCLike.re (inner ℂ a a : ℂ) := norm_sq_eq_re_inner (𝕜 := ℂ) a
    have h2 : (inner ℂ a a : ℂ) = inner ℂ (T a) u := by
      rw [hadef, LinearMap.adjoint_inner_right]
    have h3 : RCLike.re (inner ℂ (T a) u : ℂ) ≤ ‖a‖ * ‖u‖ := by
      calc RCLike.re (inner ℂ (T a) u : ℂ) ≤ ‖(inner ℂ (T a) u : ℂ)‖ := RCLike.re_le_norm _
        _ ≤ ‖T a‖ * ‖u‖ := norm_inner_le_norm _ _
        _ ≤ ‖a‖ * ‖u‖ := mul_le_mul_of_nonneg_right (hTnorm a) (norm_nonneg u)
    rw [h2] at h1
    nlinarith [norm_nonneg a, norm_nonneg u]
  · intro y
    rw [Matrix.conjTranspose_conjTranspose, hVclin]
    exact hTnorm y

omit [DecidableEq n] in
/-- The Hilbert–Schmidt norm of a matrix as the sum of the squared norms of its columns. -/
theorem trace_conjTranspose_mul_self_re (Y : Matrix n m ℂ) :
    (Matrix.trace (Yᴴ * Y)).re
      = ∑ i : m, ‖Matrix.toEuclideanLin Y (EuclideanSpace.single i (1 : ℂ))‖ ^ 2 := by
  have h1 : ∀ i : m, ‖Matrix.toEuclideanLin Y (EuclideanSpace.single i (1 : ℂ))‖ ^ 2
      = ∑ j : n, ‖Y j i‖ ^ 2 := by
    intro i
    rw [Matrix.toLpLin_apply, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
    congr 1
    ext j
    simp [Matrix.mulVec_single]
  simp only [h1, Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diag_apply,
    Complex.re_sum, Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

/-- For a positive semidefinite `P` and a matrix `X` whose adjoint is a contraction,
`tr (Xᴴ P X) ≤ tr P`. -/
theorem trace_conj_contraction_le {P X : Matrix n n ℂ} (hP : P.PosSemidef)
    (hX : ∀ y : EuclideanSpace ℂ n, ‖Matrix.toEuclideanLin Xᴴ y‖ ≤ ‖y‖) :
    (Matrix.trace (Xᴴ * P * X)).re ≤ (Matrix.trace P).re := by
  set Q := CFC.sqrt P with hQdef
  have hQh : Qᴴ = Q := (CFC.sqrt_nonneg P).posSemidef.1
  have hQQ : Q * Q = P := CFC.sqrt_mul_sqrt_self _ hP.nonneg
  have key : Matrix.trace (Xᴴ * P * X) = Matrix.trace ((Xᴴ * Q)ᴴ * (Xᴴ * Q)) := by
    have e1 : (Xᴴ * Q)ᴴ * (Xᴴ * Q) = Q * (X * Xᴴ * Q) := by
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hQh]
      noncomm_ring
    rw [e1, Matrix.trace_mul_comm Q (X * Xᴴ * Q), ← hQQ,
      Matrix.trace_mul_comm (Xᴴ * (Q * Q)) X]
    congr 1
    noncomm_ring
  rw [key, trace_conjTranspose_mul_self_re]
  have h2 : (Matrix.trace P).re = ∑ i : n, ‖Matrix.toEuclideanLin Q
      (EuclideanSpace.single i (1 : ℂ))‖ ^ 2 := by
    rw [← trace_conjTranspose_mul_self_re, hQh, hQQ]
  rw [h2]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [show Matrix.toEuclideanLin (Xᴴ * Q)
      = (Matrix.toEuclideanLin Xᴴ).comp (Matrix.toEuclideanLin Q) from
      Matrix.toLpLin_mul 2 2 2 _ _]
  simp only [LinearMap.comp_apply]
  gcongr
  exact hX _

/-- Duality bound for contractions: `|tr (M X)| ≤ tr √(Mᴴ M)` whenever `Xᴴ` is a
contraction. -/
theorem norm_trace_mul_contraction_le (M X : Matrix n n ℂ)
    (hX : ∀ y : EuclideanSpace ℂ n, ‖Matrix.toEuclideanLin Xᴴ y‖ ≤ ‖y‖) :
    ‖Matrix.trace (M * X)‖ ≤ (Matrix.trace (CFC.sqrt (Mᴴ * M))).re := by
  obtain ⟨W, hW, hM⟩ := exists_unitary_mul_sqrt M
  set P := CFC.sqrt (Mᴴ * M) with hPdef
  have hPpsd : P.PosSemidef := (CFC.sqrt_nonneg (Mᴴ * M)).posSemidef
  set Q := CFC.sqrt P with hQdef
  have hQh : Qᴴ = Q := (CFC.sqrt_nonneg P).posSemidef.1
  have hQQ : Q * Q = P := CFC.sqrt_mul_sqrt_self _ hPpsd.nonneg
  have hWstar' : W * Wᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hW
  have htr : Matrix.trace (M * X) = Matrix.trace (Qᴴ * (Q * X * W)) := by
    rw [hM, hQh]
    rw [show W * P * X = W * (Q * (Q * X)) by rw [← hQQ]; noncomm_ring]
    rw [Matrix.trace_mul_comm W (Q * (Q * X))]
    congr 1
    noncomm_ring
  have h1 : Matrix.trace (Qᴴ * Q) = Matrix.trace P := by rw [hQh, hQQ]
  have h2 : Matrix.trace ((Q * X * W)ᴴ * (Q * X * W)) = Matrix.trace (Xᴴ * P * X) := by
    have e1 : (Q * X * W)ᴴ * (Q * X * W) = Wᴴ * ((Xᴴ * P * X) * W) := by
      simp only [Matrix.conjTranspose_mul, hQh]
      rw [← hQQ]; noncomm_ring
    rw [e1, Matrix.trace_mul_comm Wᴴ ((Xᴴ * P * X) * W), Matrix.mul_assoc, hWstar',
      Matrix.mul_one]
  have hnn : (0:ℝ) ≤ (Matrix.trace P).re := by
    have hle := hPpsd.trace_nonneg
    simpa using (Complex.le_def.mp hle).1
  calc ‖Matrix.trace (M * X)‖
      = ‖Matrix.trace (Qᴴ * (Q * X * W))‖ := by rw [htr]
    _ ≤ Real.sqrt (Matrix.trace (Qᴴ * Q)).re *
          Real.sqrt (Matrix.trace ((Q * X * W)ᴴ * (Q * X * W))).re :=
        norm_trace_conjTranspose_mul_le _ _
    _ ≤ Real.sqrt (Matrix.trace P).re * Real.sqrt (Matrix.trace P).re := by
        rw [h1, h2]
        exact mul_le_mul_of_nonneg_left
          (Real.sqrt_le_sqrt (trace_conj_contraction_le hPpsd hX)) (Real.sqrt_nonneg _)
    _ = (Matrix.trace P).re := Real.mul_self_sqrt hnn

/-- The fidelity dominates the overlap of any two purifications, with an ancilla of
arbitrary dimension (matrix form). -/
theorem norm_trace_le_fidelity {ρ σ : Matrix n n ℂ} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    {A B : Matrix n m ℂ} (hA : A * Aᴴ = ρ) (hB : B * Bᴴ = σ) :
    ‖Matrix.trace (Aᴴ * B)‖ ≤ fidelity ρ σ := by
  set R := CFC.sqrt ρ with hRdef
  set S := CFC.sqrt σ with hSdef
  have hRh : Rᴴ = R := (CFC.sqrt_nonneg ρ).posSemidef.1
  have hSh : Sᴴ = S := (CFC.sqrt_nonneg σ).posSemidef.1
  have hRR : R * R = ρ := CFC.sqrt_mul_sqrt_self _ hρ.nonneg
  have hSS : S * S = σ := CFC.sqrt_mul_sqrt_self _ hσ.nonneg
  set M := S * R with hMdef
  have hMM : Mᴴ * M = R * σ * R := by
    rw [hMdef, Matrix.conjTranspose_mul, hRh, hSh, ← hSS]
    noncomm_ring
  have hfid : fidelity ρ σ = (Matrix.trace (CFC.sqrt (Mᴴ * M))).re := by
    rw [fidelity, hMM, ← hRdef]
  obtain ⟨V, hAV, hV, hVadj⟩ : ∃ V : Matrix n m ℂ, A = R * V ∧
      (∀ z : EuclideanSpace ℂ m, ‖Matrix.toEuclideanLin V z‖ ≤ ‖z‖) ∧
      (∀ y : EuclideanSpace ℂ n, ‖Matrix.toEuclideanLin Vᴴ y‖ ≤ ‖y‖) := by
    refine exists_contraction_of_mul_conjTranspose_eq ?_
    rw [hA, hRh, hRR]
  obtain ⟨W, hBW, hW, hWadj⟩ : ∃ W : Matrix n m ℂ, B = S * W ∧
      (∀ z : EuclideanSpace ℂ m, ‖Matrix.toEuclideanLin W z‖ ≤ ‖z‖) ∧
      (∀ y : EuclideanSpace ℂ n, ‖Matrix.toEuclideanLin Wᴴ y‖ ≤ ‖y‖) := by
    refine exists_contraction_of_mul_conjTranspose_eq ?_
    rw [hB, hSh, hSS]
  -- the overlap is `tr (M X)` for the contraction `X = V Wᴴ`
  have e : (Aᴴ * B)ᴴ = Wᴴ * (S * R * V) := by
    rw [hAV, hBW]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hRh, hSh,
      Matrix.mul_assoc]
  have hconj : Matrix.trace ((Aᴴ * B)ᴴ) = Matrix.trace (M * (V * Wᴴ)) := by
    rw [e, Matrix.trace_mul_comm, hMdef, Matrix.mul_assoc]
  have hnorm : ‖Matrix.trace (Aᴴ * B)‖ = ‖Matrix.trace (M * (V * Wᴴ))‖ := by
    rw [← hconj, Matrix.trace_conjTranspose, norm_star]
  have hX : ∀ y : EuclideanSpace ℂ n, ‖Matrix.toEuclideanLin (V * Wᴴ)ᴴ y‖ ≤ ‖y‖ := by
    intro y
    have happ : Matrix.toEuclideanLin ((V * Wᴴ)ᴴ) y
        = Matrix.toEuclideanLin W (Matrix.toEuclideanLin Vᴴ y) := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        show Matrix.toEuclideanLin (W * Vᴴ)
          = (Matrix.toEuclideanLin W).comp (Matrix.toEuclideanLin Vᴴ) from
          Matrix.toLpLin_mul 2 2 2 _ _]
      simp only [LinearMap.comp_apply]
    rw [happ]
    exact le_trans (hW _) (hVadj y)
  rw [hnorm, hfid]
  exact norm_trace_mul_contraction_le M (V * Wᴴ) hX

/-- **Uhlmann's theorem, upper bound with an arbitrary ancilla**: the overlap of any
purification of `ρ` with any purification of `σ` is at most the fidelity `F(ρ, σ)`, no
matter how large the ancilla is. -/
theorem norm_inner_le_fidelity {ρ σ : Matrix n n ℂ} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    {v w : EuclideanSpace ℂ (n × m)} (hv : IsPurification v ρ) (hw : IsPurification w σ) :
    ‖(inner ℂ v w : ℂ)‖ ≤ fidelity ρ σ := by
  have hv' : vecToMat v * (vecToMat v)ᴴ = ρ := by
    rw [← isPurification_matToVec_iff, matToVec_vecToMat]; exact hv
  have hw' : vecToMat w * (vecToMat w)ᴴ = σ := by
    rw [← isPurification_matToVec_iff, matToVec_vecToMat]; exact hw
  have hle := norm_trace_le_fidelity hρ hσ hv' hw'
  rwa [← inner_matToVec, matToVec_vecToMat, matToVec_vecToMat] at hle

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

