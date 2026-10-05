import Mathlib

/-!
# Commuting Simultaneous
Category: Quantum Physics
Target: QPhys.commuting_simultaneous
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Module Module.End Submodule

namespace QPhys

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- A nonzero vector in the `μ`-eigenspace of a symmetric (Hermitian) operator witnesses that `μ`
is a genuine eigenvalue, and hence that `μ` is real. -/

lemma finite_nontrivial_jointEigenspace_index :
    Finite {p : 𝕜 × 𝕜 // (eigenspace A p.2 ⊓ eigenspace B p.1 : Submodule 𝕜 E) ≠ ⊥} := by
  have key : ∀ p : {p : 𝕜 × 𝕜 // (eigenspace A p.2 ⊓ eigenspace B p.1 : Submodule 𝕜 E) ≠ ⊥},
      Module.End.HasEigenvalue A p.1.2 ∧ Module.End.HasEigenvalue B p.1.1 := by
    rintro ⟨⟨b, a⟩, hp⟩
    constructor
    · rw [Module.End.hasEigenvalue_iff]
      intro h
      exact hp (by simp [h])
    · rw [Module.End.hasEigenvalue_iff]
      intro h
      exact hp (by simp [h])
  haveI : Finite {μ : 𝕜 // Module.End.HasEigenvalue A μ} :=
    (Module.End.finite_hasEigenvalue A).to_subtype
  haveI : Finite {μ : 𝕜 // Module.End.HasEigenvalue B μ} :=
    (Module.End.finite_hasEigenvalue B).to_subtype
  refine Finite.of_injective
    (fun p ↦ ((⟨p.1.2, (key p).1⟩ : {μ : 𝕜 // Module.End.HasEigenvalue A μ}),
      (⟨p.1.1, (key p).2⟩ : {μ : 𝕜 // Module.End.HasEigenvalue B μ}))) ?_
  rintro ⟨⟨b₁, a₁⟩, h₁⟩ ⟨⟨b₂, a₂⟩, h₂⟩ h
  simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
  simp [h.1, h.2]

/-- **Commuting Hermitian operators are simultaneously diagonalizable.**

If `A` and `B` are commuting symmetric (self-adjoint, i.e. Hermitian) linear operators on a
finite-dimensional complex (or real) inner product space `E`, then `E` admits an orthonormal basis
consisting of vectors that are simultaneously eigenvectors of `A` and of `B`, with real
eigenvalues. -/
