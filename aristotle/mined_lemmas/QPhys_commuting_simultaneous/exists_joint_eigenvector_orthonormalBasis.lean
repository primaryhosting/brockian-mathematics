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
