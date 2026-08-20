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
