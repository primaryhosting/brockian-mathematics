/-!
# Commuting Simultaneous
Category: Quantum Physics
Target: QPhys.commuting_simultaneous
Statement: Two commuting Hermitian operators are simultaneously diagonalizable.
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-
# Commuting Simultaneous
Category: Quantum Physics
Target: QPhys.commuting_simultaneous
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


/-!
# Commuting Simultaneous
Category: Quantum Physics
Target: QPhys.commuting_simultaneous
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Module (finrank)
open Module.End

namespace QPhys

/-- **Two commuting Hermitian operators are simultaneously diagonalizable.**

Given two symmetric (Hermitian / self-adjoint) linear operators `A` and `B` on a
finite-dimensional inner product space `E` over `𝕜 = ℝ` or `ℂ`, which commute,
there exists an orthonormal basis `v` of `E` consisting of joint eigenvectors:
each `v i` is an eigenvector of `A` with eigenvalue `a i` and simultaneously an
eigenvector of `B` with eigenvalue `b i`.

The key input is Mathlib's
`LinearMap.IsSymmetric.directSum_isInternal_of_commute`, which decomposes `E` as
an internal direct sum of the joint eigenspaces, together with
`DirectSum.IsInternal.subordinateOrthonormalBasis`, which produces an orthonormal
basis subordinate to such a decomposition. -/
theorem commuting_simultaneous
    {𝕜 : Type*} {E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E] {n : ℕ} (hn : finrank 𝕜 E = n)
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric) (hAB : Commute A B) :
    ∃ (v : OrthonormalBasis (Fin n) 𝕜 E) (a b : Fin n → 𝕜),
      ∀ i, A (v i) = a i • v i ∧ B (v i) = b i • v i := by
  classical
  set V : 𝕜 × 𝕜 → Submodule 𝕜 E := fun i => eigenspace A i.2 ⊓ eigenspace B i.1 with hV_def
  have hV : DirectSum.IsInternal V := hA.directSum_isInternal_of_commute hB hAB
  have hVfam : OrthogonalFamily 𝕜 (fun i => V i) fun i => (V i).subtypeₗᵢ :=
    hA.orthogonalFamily_eigenspace_inf_eigenspace hB
  -- restrict to the (finitely many) indices with nonzero joint eigenspace
  have hfin : Set.Finite {i : 𝕜 × 𝕜 | V i ≠ ⊥} :=
    WellFoundedGT.finite_ne_bot_of_iSupIndep
      ((DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top V).mp hV).1
  have : Fintype {i : 𝕜 × 𝕜 // V i ≠ ⊥} := hfin.fintype
  set W : {i : 𝕜 × 𝕜 // V i ≠ ⊥} → Submodule 𝕜 E := fun i => V i.1 with hW_def
  have hW : DirectSum.IsInternal W := DirectSum.isInternal_ne_bot_iff.mpr hV
  have hWfam : OrthogonalFamily 𝕜 (fun i => W i) fun i => (W i).subtypeₗᵢ :=
    hVfam.comp Subtype.val_injective
  refine ⟨hW.subordinateOrthonormalBasis hn hWfam,
    fun i => (hW.subordinateOrthonormalBasisIndex hn i hWfam).val.2,
    fun i => (hW.subordinateOrthonormalBasisIndex hn i hWfam).val.1, fun i => ?_⟩
  obtain ⟨hmA, hmB⟩ := hW.subordinateOrthonormalBasis_subordinate hn i hWfam
  exact ⟨mem_eigenspace_iff.mp hmA, mem_eigenspace_iff.mp hmB⟩

end QPhys


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

