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

set_option maxHeartbeats 1000000

namespace QPhys

open Module Module.End Submodule

/-- **Two commuting Hermitian operators are simultaneously diagonalizable.**

If `A` and `B` are symmetric (Hermitian, self-adjoint) linear operators on a
finite-dimensional inner product space `E` over `𝕜 = ℝ` or `ℂ`, and they commute
(`A ∘ₗ B = B ∘ₗ A`), then there is an orthonormal basis of `E` each of whose vectors is
simultaneously an eigenvector of `A` and of `B`; in that basis both operators are diagonal.

The proof assembles Mathlib's joint-eigenspace decomposition
`LinearMap.IsSymmetric.directSum_isInternal_of_commute` (the space is the internal direct
sum of the joint eigenspaces `eigenspace A ν ⊓ eigenspace B μ`) with the fact that these
joint eigenspaces form an orthogonal family
(`LinearMap.IsSymmetric.orthogonalFamily_eigenspace_inf_eigenspace`), and then picks an
orthonormal basis subordinate to that decomposition
(`DirectSum.IsInternal.subordinateOrthonormalBasis`). Since only finitely many joint
eigenspaces are nonzero, the index type can be cut down to a finite one. -/
theorem commuting_simultaneous {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] {A B : E →ₗ[𝕜] E}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) (hAB : A ∘ₗ B = B ∘ₗ A) :
    ∃ v : OrthonormalBasis (Fin (finrank 𝕜 E)) 𝕜 E,
      ∀ i, ∃ a b : 𝕜, A (v i) = a • v i ∧ B (v i) = b • v i := by
  classical
  have hC : Commute A B := hAB
  set V : 𝕜 × 𝕜 → Submodule 𝕜 E := fun p => eigenspace A p.2 ⊓ eigenspace B p.1 with hVdef
  have hInt : DirectSum.IsInternal V := hA.directSum_isInternal_of_commute hB hC
  have hIndep : iSupIndep V :=
    ((DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top V).mp hInt).1
  letI : Fintype {p : 𝕜 × 𝕜 // V p ≠ ⊥} := hIndep.fintypeNeBotOfFiniteDimensional
  have hInt' : DirectSum.IsInternal (fun i : {p : 𝕜 × 𝕜 // V p ≠ ⊥} => V i) :=
    DirectSum.isInternal_ne_bot_iff.mpr hInt
  have hOF := hA.orthogonalFamily_eigenspace_inf_eigenspace hB
  have hOF' : OrthogonalFamily 𝕜 (fun i : {p : 𝕜 × 𝕜 // V p ≠ ⊥} => (V i : Submodule 𝕜 E))
      (fun i => (V i).subtypeₗᵢ) := hOF.comp Subtype.val_injective
  refine ⟨hInt'.subordinateOrthonormalBasis rfl hOF', fun i => ?_⟩
  have hmem := hInt'.subordinateOrthonormalBasis_subordinate (hV' := hOF') (hn := rfl) i
  set p := hInt'.subordinateOrthonormalBasisIndex rfl i hOF'
  exact ⟨p.1.2, p.1.1, mem_eigenspace_iff.mp hmem.1, mem_eigenspace_iff.mp hmem.2⟩

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

