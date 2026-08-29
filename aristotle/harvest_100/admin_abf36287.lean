/-
# Commuting Simultaneous
Category: Quantum Physics
Target: QPhys.commuting_simultaneous
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open Module LinearMap

namespace QPhys

/-- **Commuting Hermitian operators are simultaneously diagonalizable.**

If `A` and `B` are symmetric (Hermitian) linear operators on a finite-dimensional inner
product space `E` over `𝕜 = ℝ` or `ℂ` with `finrank 𝕜 E = n`, and if `A` and `B` commute,
then `E` admits an orthonormal basis `v : Fin n → E` all of whose vectors are simultaneously
eigenvectors of `A` (with eigenvalue `a i`) and of `B` (with eigenvalue `b i`).  In other
words `A` and `B` are diagonal in one and the same orthonormal basis.

The proof combines the joint-eigenspace decomposition
`LinearMap.IsSymmetric.directSum_isInternal_of_commute` (restricted to the finitely many
nonzero joint eigenspaces) with `DirectSum.IsInternal.subordinateOrthonormalBasis`. -/
theorem commuting_simultaneous {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] {n : ℕ} (hn : finrank 𝕜 E = n)
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric) (hAB : Commute A B) :
    ∃ (v : OrthonormalBasis (Fin n) 𝕜 E) (a b : Fin n → 𝕜),
      ∀ i, A (v i) = a i • v i ∧ B (v i) = b i • v i := by
  classical
  -- The joint eigenspaces of `A` and `B`.
  set V : 𝕜 × 𝕜 → Submodule 𝕜 E :=
    fun i ↦ Module.End.eigenspace A i.2 ⊓ Module.End.eigenspace B i.1
  have hV : DirectSum.IsInternal V :=
    LinearMap.IsSymmetric.directSum_isInternal_of_commute hA hB hAB
  have hV' : OrthogonalFamily 𝕜 (fun i ↦ (V i : Submodule 𝕜 E)) (fun i ↦ (V i).subtypeₗᵢ) :=
    LinearMap.IsSymmetric.orthogonalFamily_eigenspace_inf_eigenspace hA hB
  have hind : iSupIndep V := hV.submodule_iSupIndep
  -- Only finitely many joint eigenspaces are nonzero; restrict to those.
  letI : Fintype { i : 𝕜 × 𝕜 // V i ≠ ⊥ } := hind.fintypeNeBotOfFiniteDimensional
  set W : { i : 𝕜 × 𝕜 // V i ≠ ⊥ } → Submodule 𝕜 E := fun j ↦ V j.1
  have hWsup : iSup W = ⊤ := by
    refine le_antisymm le_top ?_
    rw [← hV.submodule_iSup_eq_top]
    refine iSup_le fun i ↦ ?_
    by_cases h : V i = ⊥
    · simp [h]
    · exact le_iSup W ⟨i, h⟩
  have hW : DirectSum.IsInternal W :=
    (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top W).mpr
      ⟨hind.comp Subtype.val_injective, hWsup⟩
  have hW' : OrthogonalFamily 𝕜 (fun j ↦ (W j : Submodule 𝕜 E)) (fun j ↦ (W j).subtypeₗᵢ) :=
    hV'.comp Subtype.val_injective
  refine ⟨hW.subordinateOrthonormalBasis hn hW',
    fun i ↦ ((hW.subordinateOrthonormalBasisIndex hn i hW' : { i : 𝕜 × 𝕜 // V i ≠ ⊥ }) : 𝕜 × 𝕜).2,
    fun i ↦ ((hW.subordinateOrthonormalBasisIndex hn i hW' : { i : 𝕜 × 𝕜 // V i ≠ ⊥ }) : 𝕜 × 𝕜).1,
    fun i ↦ ?_⟩
  have hmem := hW.subordinateOrthonormalBasis_subordinate hn i hW'
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.mp hmem
  exact ⟨Module.End.mem_eigenspace_iff.mp h1, Module.End.mem_eigenspace_iff.mp h2⟩

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

