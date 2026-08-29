import Mathlib
/-!
# Commuting Simultaneous
Category: Quantum Physics
Target: QPhys.commuting_simultaneous
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Module

namespace QPhys

/-- **Two commuting Hermitian operators are simultaneously diagonalizable.**

If `A` and `B` are Hermitian (symmetric / self-adjoint) operators on a finite-dimensional
complex inner product space `E` with `A * B = B * A`, then there is an orthonormal basis of
`E` consisting of vectors that are simultaneously eigenvectors of `A` and of `B`; the
corresponding eigenvalue functions are `a` (for `A`) and `c` (for `B`). -/
theorem commuting_simultaneous
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    {A B : E →ₗ[ℂ] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric) (hAB : Commute A B) :
    ∃ (b : OrthonormalBasis (Fin (finrank ℂ E)) ℂ E) (a c : Fin (finrank ℂ E) → ℂ),
      ∀ i, A (b i) = a i • b i ∧ B (b i) = c i • b i := by
  classical
  -- The joint eigenspaces of `A` and `B`, indexed by pairs of scalars.
  set V : ℂ × ℂ → Submodule ℂ E :=
    fun p => Module.End.eigenspace A p.2 ⊓ Module.End.eigenspace B p.1 with hVdef
  have hVint : DirectSum.IsInternal V := hA.directSum_isInternal_of_commute hB hAB
  have hVorth : OrthogonalFamily ℂ (fun p : ℂ × ℂ => ↥(V p))
      (fun p : ℂ × ℂ => (V p).subtypeₗᵢ) :=
    hA.orthogonalFamily_eigenspace_inf_eigenspace hB
  obtain ⟨hindep, htop⟩ :=
    (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top V).mp hVint
  -- Restrict to the (finitely many) nonzero joint eigenspaces, to get a finite index type.
  letI : Fintype {p : ℂ × ℂ // V p ≠ ⊥} := hindep.fintypeNeBotOfFiniteDimensional
  set W : {p : ℂ × ℂ // V p ≠ ⊥} → Submodule ℂ E := fun i => V i.1 with hWdef
  have hWint : DirectSum.IsInternal W := by
    refine (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top W).mpr
      ⟨hindep.comp Subtype.coe_injective, ?_⟩
    rw [hWdef, iSup_ne_bot_subtype, htop]
  have hWorth : OrthogonalFamily ℂ (fun i : {p : ℂ × ℂ // V p ≠ ⊥} => ↥(W i))
      (fun i => (W i).subtypeₗᵢ) := hVorth.comp Subtype.coe_injective
  refine ⟨hWint.subordinateOrthonormalBasis rfl hWorth,
    fun i => (hWint.subordinateOrthonormalBasisIndex rfl i hWorth).1.2,
    fun i => (hWint.subordinateOrthonormalBasisIndex rfl i hWorth).1.1, fun i => ?_⟩
  have hmem := hWint.subordinateOrthonormalBasis_subordinate rfl i hWorth
  obtain ⟨hA', hB'⟩ := Submodule.mem_inf.mp hmem
  exact ⟨Module.End.mem_eigenspace_iff.mp hA', Module.End.mem_eigenspace_iff.mp hB'⟩

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

