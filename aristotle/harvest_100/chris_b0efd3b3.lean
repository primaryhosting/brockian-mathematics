import Mathlib

/-!
# Commuting Simultaneous
Category: Quantum Physics
Target: QPhys.commuting_simultaneous
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QPhys

open Matrix Module.End

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### A common orthonormal eigenbasis for two commuting symmetric operators -/

omit [DecidableEq n] in
/-- Two commuting symmetric operators on a finite-dimensional complex inner product space
have a common orthonormal eigenbasis. -/
lemma exists_joint_eigenvector_orthonormalBasis {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (hdim : Module.finrank ℂ E = Fintype.card n)
    (TA TB : E →ₗ[ℂ] E) (hTA : TA.IsSymmetric) (hTB : TB.IsSymmetric) (hcomm : Commute TA TB) :
    ∃ b : OrthonormalBasis n ℂ E, ∀ j, ∃ α β : ℂ, TA (b j) = α • b j ∧ TB (b j) = β • b j := by
  classical
  set V : ℂ × ℂ → Submodule ℂ E := fun i => eigenspace TA i.2 ⊓ eigenspace TB i.1 with hV
  have hof : OrthogonalFamily ℂ (fun i => (V i : Submodule ℂ E)) fun i => (V i).subtypeₗᵢ :=
    LinearMap.IsSymmetric.orthogonalFamily_eigenspace_inf_eigenspace hTA hTB
  have hint : DirectSum.IsInternal V := hTA.directSum_isInternal_of_commute hTB hcomm
  letI : Fintype {i // V i ≠ ⊥} := hint.submodule_iSupIndep.fintypeNeBotOfFiniteDimensional
  -- restrict the family of joint eigenspaces to the (finitely many) nonzero ones
  set V' : {i // V i ≠ ⊥} → Submodule ℂ E := fun i => V i.1 with hV'
  have hof' : OrthogonalFamily ℂ (fun i => (V' i : Submodule ℂ E)) fun i => (V' i).subtypeₗᵢ :=
    hof.comp (f := Subtype.val) Subtype.val_injective
  have hsup : (⨆ i, V' i) = ⨆ i, V i := by
    refine le_antisymm (iSup_le fun i => le_iSup V i.1) (iSup_le fun i => ?_)
    by_cases h : V i = ⊥
    · simp [h]
    · exact le_iSup V' ⟨i, h⟩
  have hint' : DirectSum.IsInternal V' := by
    rw [hof'.isInternal_iff, hsup]
    exact hof.isInternal_iff.1 hint
  refine ⟨(hint'.subordinateOrthonormalBasis hdim hof').reindex (Fintype.equivFin n).symm, ?_⟩
  intro j
  have hsub := hint'.subordinateOrthonormalBasis_subordinate hdim (Fintype.equivFin n j) hof'
  set i := hint'.subordinateOrthonormalBasisIndex hdim (Fintype.equivFin n j) hof' with hi
  refine ⟨i.1.2, i.1.1, ?_, ?_⟩ <;>
  · simp only [OrthonormalBasis.reindex_apply, Equiv.symm_symm]
    obtain ⟨h1, h2⟩ := hsub
    first
      | exact mem_eigenspace_iff.1 h1
      | exact mem_eigenspace_iff.1 h2

/-- Eigenvalues of a symmetric operator are real. -/
lemma re_eigenvalue_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric) {x : E} (hx : x ≠ 0) {c : ℂ} (h : T x = c • x) :
    (c.re : ℂ) = c :=
  Complex.conj_eq_iff_re.1 (hT.conj_eigenvalue_eq_self
    (hasEigenvalue_of_hasEigenvector ⟨mem_eigenspace_iff.2 h, hx⟩))

omit [DecidableEq n] in
/-- Two commuting symmetric operators on a finite-dimensional complex inner product space have
a common orthonormal eigenbasis, with real eigenvalues. -/
lemma exists_joint_eigenbasis_real {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (hdim : Module.finrank ℂ E = Fintype.card n)
    (TA TB : E →ₗ[ℂ] E) (hTA : TA.IsSymmetric) (hTB : TB.IsSymmetric) (hcomm : Commute TA TB) :
    ∃ (b : OrthonormalBasis n ℂ E) (a c : n → ℝ),
      (∀ j, TA (b j) = (a j : ℂ) • b j) ∧ (∀ j, TB (b j) = (c j : ℂ) • b j) := by
  obtain ⟨b, hb⟩ := exists_joint_eigenvector_orthonormalBasis hdim TA TB hTA hTB hcomm
  have key : ∀ j, ∃ p : ℝ × ℝ, TA (b j) = (p.1 : ℂ) • b j ∧ TB (b j) = (p.2 : ℂ) • b j := by
    intro j
    obtain ⟨α, β, h1, h2⟩ := hb j
    have hbj : b j ≠ 0 := b.toBasis.ne_zero j
    exact ⟨(α.re, β.re), by rw [re_eigenvalue_eq hTA hbj h1]; exact h1,
      by rw [re_eigenvalue_eq hTB hbj h2]; exact h2⟩
  choose p hp₁ hp₂ using key
  exact ⟨b, fun j => (p j).1, fun j => (p j).2, hp₁, hp₂⟩

/-! ### Passing from operators to matrices -/

/-- The change-of-basis matrix from the standard basis of `EuclideanSpace ℂ n` to an
orthonormal basis `b`; its columns are the vectors `b j`. -/
noncomputable def obMatrix (b : OrthonormalBasis n ℂ (EuclideanSpace ℂ n)) : Matrix n n ℂ :=
  (EuclideanSpace.basisFun n ℂ).toBasis.toMatrix b.toBasis

lemma obMatrix_mem_unitaryGroup (b : OrthonormalBasis n ℂ (EuclideanSpace ℂ n)) :
    obMatrix b ∈ Matrix.unitaryGroup n ℂ :=
  (EuclideanSpace.basisFun n ℂ).toMatrix_orthonormalBasis_mem_unitary b

lemma obMatrix_mulVec_single (b : OrthonormalBasis n ℂ (EuclideanSpace ℂ n)) (j : n) :
    obMatrix b *ᵥ Pi.single j 1 = ⇑(b j) := by
  rw [mulVec_single_one]; rfl

lemma conjTranspose_obMatrix_mulVec (b : OrthonormalBasis n ℂ (EuclideanSpace ℂ n)) (j : n) :
    (obMatrix b)ᴴ *ᵥ ⇑(b j) = Pi.single j 1 := by
  have h1 : (obMatrix b)ᴴ * obMatrix b = 1 := by
    have := (Matrix.mem_unitaryGroup_iff' (A := obMatrix b)).1 (obMatrix_mem_unitaryGroup b)
    simpa [Matrix.star_eq_conjTranspose] using this
  rw [← obMatrix_mulVec_single b j, mulVec_mulVec, h1, one_mulVec]

/-- If every vector of an orthonormal basis `b` is an eigenvector of `M`, then conjugating `M`
by the unitary matrix `obMatrix b` diagonalizes `M`. -/
lemma conj_eq_diagonal (b : OrthonormalBasis n ℂ (EuclideanSpace ℂ n)) (M : Matrix n n ℂ)
    (d : n → ℂ) (h : ∀ j, M *ᵥ ⇑(b j) = d j • ⇑(b j)) :
    (obMatrix b)ᴴ * M * obMatrix b = Matrix.diagonal d := by
  have hcol : ∀ j, ((obMatrix b)ᴴ * M * obMatrix b) *ᵥ Pi.single j 1 = Pi.single j (d j) := by
    intro j
    rw [← mulVec_mulVec, ← mulVec_mulVec, obMatrix_mulVec_single, h j, mulVec_smul,
      conjTranspose_obMatrix_mulVec]
    ext i
    simp [Pi.single_apply]
  ext i j
  have h1 := congrFun (hcol j) i
  rw [mulVec_single_one] at h1
  by_cases hij : i = j
  · subst hij; simpa using h1
  · rw [Matrix.diagonal_apply_ne _ hij]
    simpa [Pi.single_apply, hij] using h1

lemma commute_toEuclideanLin {A B : Matrix n n ℂ} (hAB : A * B = B * A) :
    Commute (Matrix.toEuclideanLin A) (Matrix.toEuclideanLin B) := by
  unfold Commute SemiconjBy
  ext x i
  simp only [Module.End.mul_apply, Matrix.toEuclideanLin, Matrix.toLpLin_apply, WithLp.ofLp_toLp]
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hAB]

lemma mulVec_of_toEuclideanLin_eq (A : Matrix n n ℂ) {x : EuclideanSpace ℂ n} {c : ℂ}
    (h : Matrix.toEuclideanLin A x = c • x) : A *ᵥ ⇑x = c • ⇑x := by
  simpa [Matrix.toEuclideanLin, Matrix.toLpLin_apply] using congrArg WithLp.ofLp h

/-- Two commuting Hermitian matrices have a common orthonormal eigenbasis, with real
eigenvalues. -/
lemma exists_joint_eigenbasis {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hAB : A * B = B * A) :
    ∃ (b : OrthonormalBasis n ℂ (EuclideanSpace ℂ n)) (a c : n → ℝ),
      (∀ j, A *ᵥ ⇑(b j) = (a j : ℂ) • ⇑(b j)) ∧ (∀ j, B *ᵥ ⇑(b j) = (c j : ℂ) • ⇑(b j)) := by
  obtain ⟨b, a, c, ha, hc⟩ := exists_joint_eigenbasis_real
    (E := EuclideanSpace ℂ n) finrank_euclideanSpace _ _
    (Matrix.isHermitian_iff_isSymmetric.1 hA) (Matrix.isHermitian_iff_isSymmetric.1 hB)
    (commute_toEuclideanLin hAB)
  exact ⟨b, a, c, fun j => mulVec_of_toEuclideanLin_eq A (ha j),
    fun j => mulVec_of_toEuclideanLin_eq B (hc j)⟩

/-- **Commuting Hermitian operators are simultaneously diagonalizable.**
Given two commuting Hermitian matrices `A` and `B` there is a single unitary matrix `U` and
real vectors `a`, `c` such that `Uᴴ A U` and `Uᴴ B U` are the diagonal matrices with diagonals
`a` and `c`. -/
theorem commuting_simultaneous {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hAB : A * B = B * A) :
    ∃ (U : Matrix n n ℂ) (a c : n → ℝ), U ∈ Matrix.unitaryGroup n ℂ ∧
      Uᴴ * A * U = Matrix.diagonal (fun i => (a i : ℂ)) ∧
      Uᴴ * B * U = Matrix.diagonal (fun i => (c i : ℂ)) := by
  obtain ⟨b, a, c, ha, hc⟩ := exists_joint_eigenbasis hA hB hAB
  exact ⟨obMatrix b, a, c, obMatrix_mem_unitaryGroup b,
    conj_eq_diagonal b A _ ha, conj_eq_diagonal b B _ hc⟩

end QPhys

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

