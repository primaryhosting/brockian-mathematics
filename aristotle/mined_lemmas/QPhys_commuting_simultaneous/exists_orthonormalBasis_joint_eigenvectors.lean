-- Note: Lean 4 requires `import` commands to precede any doc comment, so the requested
-- header block appears immediately below the import.
import Mathlib

/-!
# Commuting Simultaneous
Category: Quantum Physics
Target: QPhys.commuting_simultaneous
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Module Submodule Module.End Matrix

namespace QPhys

/-- Two commuting symmetric (Hermitian) operators on a finite-dimensional inner product space
have a common orthonormal eigenbasis, indexed by any index type of the right cardinality. -/

theorem exists_orthonormalBasis_joint_eigenvectors
    {𝕜 E ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E] [Fintype ι] (hcard : finrank 𝕜 E = Fintype.card ι)
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric) (hAB : Commute A B) :
    ∃ v : OrthonormalBasis ι 𝕜 E, ∀ i, (∃ μ : 𝕜, A (v i) = μ • v i) ∧
      (∃ ν : 𝕜, B (v i) = ν • v i) := by
  classical
  set V : 𝕜 × 𝕜 → Submodule 𝕜 E := fun p => eigenspace A p.2 ⊓ eigenspace B p.1 with hVdef
  have hV : DirectSum.IsInternal V := hA.directSum_isInternal_of_commute hB hAB
  have hVfam : OrthogonalFamily 𝕜 (fun p => (V p : Submodule 𝕜 E)) (fun p => (V p).subtypeₗᵢ) :=
    LinearMap.IsSymmetric.orthogonalFamily_eigenspace_inf_eigenspace hA hB
  have hfin : {p | V p ≠ ⊥}.Finite :=
    WellFoundedGT.finite_ne_bot_of_iSupIndep hV.submodule_iSupIndep
  haveI : Fintype {p : 𝕜 × 𝕜 // V p ≠ ⊥} := hfin.fintype
  set W : {p : 𝕜 × 𝕜 // V p ≠ ⊥} → Submodule 𝕜 E := fun p => V p.1 with hWdef
  have hWfam : OrthogonalFamily 𝕜 (fun p => (W p : Submodule 𝕜 E)) (fun p => (W p).subtypeₗᵢ) :=
    hVfam.comp Subtype.val_injective
  have hsup : (⨆ p, W p) = ⊤ := by
    rw [hWdef, iSup_ne_bot_subtype]
    exact hV.submodule_iSup_eq_top
  have hW : DirectSum.IsInternal W := hWfam.isInternal_iff.mpr (by rw [hsup]; simp)
  refine ⟨(hW.subordinateOrthonormalBasis hcard hWfam).reindex (Fintype.equivFin ι).symm,
    fun i => ?_⟩
  have hmem := hW.subordinateOrthonormalBasis_subordinate hcard (Fintype.equivFin ι i) hWfam
  rw [OrthonormalBasis.reindex_apply, Equiv.symm_symm]
  obtain ⟨h1, h2⟩ := hmem
  exact ⟨⟨_, mem_eigenspace_iff.mp h1⟩, ⟨_, mem_eigenspace_iff.mp h2⟩⟩

/-- If the columns of the change-of-basis matrix `U` of an orthonormal basis `v` consist of
eigenvectors of `M` with eigenvalues `d`, then `U⋆ M U` is the diagonal matrix with entries `d`. -/
