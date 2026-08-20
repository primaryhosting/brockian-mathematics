/-
# Commuting Simultaneous
Category: Quantum Physics
Target: QPhys.commuting_simultaneous
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Commuting Simultaneous
Category: Quantum Physics
Target: QPhys.commuting_simultaneous
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace QPhys

open Module Module.End

/-- Restricting an internal direct sum decomposition to the indices whose summand is nonzero
still yields an internal direct sum decomposition. -/
theorem isInternal_subtype_ne_bot {𝕜 E ι : Type*} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [DecidableEq ι] (V : ι → Submodule 𝕜 E) (hV : DirectSum.IsInternal V) :
    DirectSum.IsInternal (fun i : {i : ι // V i ≠ ⊥} ↦ V i.1) := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  refine ⟨hV.submodule_iSupIndep.comp Subtype.val_injective, ?_⟩
  refine le_antisymm le_top ?_
  rw [← hV.submodule_iSup_eq_top]
  refine iSup_le fun i ↦ ?_
  by_cases hi : V i = ⊥
  · simp [hi]
  · exact le_iSup (fun j : {i : ι // V i ≠ ⊥} ↦ V j.1) ⟨i, hi⟩

/-- **Two commuting Hermitian (symmetric) operators are simultaneously diagonalizable.**

If `A` and `B` are symmetric (Hermitian) linear operators on a finite-dimensional inner
product space `E` over `𝕜 = ℝ` or `ℂ`, and they commute, then there is an orthonormal basis
of `E` each of whose vectors is simultaneously an eigenvector of `A` and of `B`.

The proof combines `LinearMap.IsSymmetric.directSum_isInternal_of_commute` (the decomposition
of `E` into an internal direct sum of joint eigenspaces of `A` and `B`) with
`DirectSum.IsInternal.subordinateOrthonormalBasis`. -/
theorem commuting_simultaneous {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] {A B : E →ₗ[𝕜] E}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) (hAB : Commute A B) :
    ∃ b : OrthonormalBasis (Fin (finrank 𝕜 E)) 𝕜 E,
      ∀ i, ∃ a c : 𝕜, A (b i) = a • b i ∧ B (b i) = c • b i := by
  have hV : DirectSum.IsInternal
      (fun i : 𝕜 × 𝕜 ↦ (eigenspace A i.2 ⊓ eigenspace B i.1 : Submodule 𝕜 E)) :=
    hA.directSum_isInternal_of_commute hB hAB
  have hV' : OrthogonalFamily 𝕜
      (fun i : 𝕜 × 𝕜 ↦ (eigenspace A i.2 ⊓ eigenspace B i.1 : Submodule 𝕜 E))
      (fun i ↦ (eigenspace A i.2 ⊓ eigenspace B i.1).subtypeₗᵢ) :=
    LinearMap.IsSymmetric.orthogonalFamily_eigenspace_inf_eigenspace hA hB
  letI : Fintype {i : 𝕜 × 𝕜 //
      (eigenspace A i.2 ⊓ eigenspace B i.1 : Submodule 𝕜 E) ≠ ⊥} :=
    hV.submodule_iSupIndep.fintypeNeBotOfFiniteDimensional
  -- Restrict to the finitely many nonzero joint eigenspaces.
  have hW : DirectSum.IsInternal (fun i : {i : 𝕜 × 𝕜 //
      (eigenspace A i.2 ⊓ eigenspace B i.1 : Submodule 𝕜 E) ≠ ⊥} ↦
        (eigenspace A i.1.2 ⊓ eigenspace B i.1.1 : Submodule 𝕜 E)) :=
    isInternal_subtype_ne_bot _ hV
  have hW' : OrthogonalFamily 𝕜 (fun i : {i : 𝕜 × 𝕜 //
      (eigenspace A i.2 ⊓ eigenspace B i.1 : Submodule 𝕜 E) ≠ ⊥} ↦
        (eigenspace A i.1.2 ⊓ eigenspace B i.1.1 : Submodule 𝕜 E))
      (fun i ↦ (eigenspace A i.1.2 ⊓ eigenspace B i.1.1).subtypeₗᵢ) :=
    hV'.comp Subtype.val_injective
  refine ⟨hW.subordinateOrthonormalBasis rfl hW', fun i ↦ ?_⟩
  have hmem := Submodule.mem_inf.mp (hW.subordinateOrthonormalBasis_subordinate rfl i hW')
  exact ⟨_, _, mem_eigenspace_iff.mp hmem.1, mem_eigenspace_iff.mp hmem.2⟩

end QPhys

#print axioms QPhys.commuting_simultaneous

