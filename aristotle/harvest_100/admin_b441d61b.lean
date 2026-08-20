import Mathlib

/-!
# Commuting Simultaneous
Category: Quantum Physics
Target: QPhys.commuting_simultaneous
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Module Module.End

namespace QPhys

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  {A B : E →ₗ[ℂ] E}

local notation "EV" => Module.End.Eigenvalues

omit [FiniteDimensional ℂ E] in
/-- The map sending a pair of eigenvalues of `A` and `B` to the corresponding pair of scalars
(in the order used by Mathlib's joint eigenspace family) is injective. -/
private theorem eigenvaluePair_injective :
    Function.Injective
      (fun p : EV (A : Module.End ℂ E) × EV (B : Module.End ℂ E) ↦ ((p.2 : ℂ), (p.1 : ℂ))) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  simp only [Prod.mk.injEq] at h
  exact Prod.ext (Subtype.ext h.2) (Subtype.ext h.1)

/-- The joint eigenspaces indexed by pairs of eigenvalues already exhaust the space. -/
private theorem iSup_joint_eigenspace_eq_top (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    (hAB : Commute A B) :
    (⨆ p : EV (A : Module.End ℂ E) × EV (B : Module.End ℂ E),
      (eigenspace A (p.1 : ℂ) ⊓ eigenspace B (p.2 : ℂ) : Submodule ℂ E)) = ⊤ := by
  rw [eq_top_iff, ← hA.iSup_iSup_eigenspace_inf_eigenspace_eq_top_of_commute hB hAB]
  refine iSup_le fun α ↦ iSup_le fun γ ↦ ?_
  by_cases hα : eigenspace A α = ⊥
  · simp [hα]
  by_cases hγ : eigenspace B γ = ⊥
  · simp [hγ]
  · exact le_iSup (fun p : EV (A : Module.End ℂ E) × EV (B : Module.End ℂ E) ↦
      (eigenspace A (p.1 : ℂ) ⊓ eigenspace B (p.2 : ℂ) : Submodule ℂ E))
      (⟨⟨α, hasEigenvalue_iff.mpr hα⟩, ⟨γ, hasEigenvalue_iff.mpr hγ⟩⟩)

end

/-- **Commuting Hermitian operators are simultaneously diagonalizable.**

If `A` and `B` are Hermitian (self-adjoint, i.e. `IsSymmetric`) operators on a
finite-dimensional complex inner product space `E` which commute, then there is an
orthonormal basis of `E` all of whose vectors are simultaneous eigenvectors of `A` and `B`,
with eigenvalues `μ i` and `ν i` respectively. -/
theorem commuting_simultaneous {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] {A B : E →ₗ[ℂ] E}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) (hAB : Commute A B) :
    ∃ (b : OrthonormalBasis (Fin (finrank ℂ E)) ℂ E) (μ ν : Fin (finrank ℂ E) → ℂ),
      ∀ i, A (b i) = μ i • b i ∧ B (b i) = ν i • b i := by
  classical
  set ι := Module.End.Eigenvalues (A : Module.End ℂ E) ×
    Module.End.Eigenvalues (B : Module.End ℂ E)
  set V : ι → Submodule ℂ E :=
    fun p ↦ (eigenspace A (p.1 : ℂ) ⊓ eigenspace B (p.2 : ℂ) : Submodule ℂ E)
  have hfam : OrthogonalFamily ℂ (fun p : ι ↦ V p) (fun p ↦ (V p).subtypeₗᵢ) :=
    OrthogonalFamily.comp
      (LinearMap.IsSymmetric.orthogonalFamily_eigenspace_inf_eigenspace hA hB)
      (f := fun p : ι ↦ ((p.2 : ℂ), (p.1 : ℂ))) eigenvaluePair_injective
  have hV : DirectSum.IsInternal V := by
    refine hfam.isInternal_iff.mpr ?_
    rw [Submodule.orthogonal_eq_bot_iff]
    exact iSup_joint_eigenspace_eq_top hA hB hAB
  refine ⟨hV.subordinateOrthonormalBasis rfl hfam,
    fun i ↦ ((hV.subordinateOrthonormalBasisIndex rfl i hfam).1 : ℂ),
    fun i ↦ ((hV.subordinateOrthonormalBasisIndex rfl i hfam).2 : ℂ), fun i ↦ ?_⟩
  obtain ⟨h1, h2⟩ := hV.subordinateOrthonormalBasis_subordinate rfl i hfam
  exact ⟨mem_eigenspace_iff.mp h1, mem_eigenspace_iff.mp h2⟩

end QPhys

#print axioms QPhys.commuting_simultaneous

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

