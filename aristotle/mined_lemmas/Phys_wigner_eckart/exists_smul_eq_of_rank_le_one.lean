/-
# Wigner Eckart
Category: Frontier Phys
Target: Phys.wigner_eckart
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Wigner Eckart
Category: Frontier Phys
Target: Phys.wigner_eckart
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped TensorProduct
open Representation

namespace Phys

variable {k G U V W : Type*} [Field k] [Group G]
  [AddCommGroup U] [Module k U] [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

/-- The space of intertwining (`G`-equivariant) linear maps between two representations,
as a subspace of all linear maps. -/

theorem exists_smul_eq_of_rank_le_one {ρ : Representation k G V} {σ : Representation k G W}
    (hmult : Module.rank k (intertwiners ρ σ) ≤ 1)
    {CG T : V →ₗ[k] W} (hCG : CG ∈ intertwiners ρ σ) (hT : T ∈ intertwiners ρ σ)
    (hCG0 : CG ≠ 0) :
    ∃ c : k, T = c • CG := by
  rw [rank_le_one_iff] at hmult
  obtain ⟨v₀, h⟩ := hmult
  obtain ⟨a, ha⟩ := h ⟨CG, hCG⟩
  obtain ⟨b, hb⟩ := h ⟨T, hT⟩
  have ha0 : a ≠ 0 := by
    rintro rfl
    apply hCG0
    have := congrArg Subtype.val ha
    simpa using this.symm
  refine ⟨b / a, ?_⟩
  have hb' : b • (v₀ : V →ₗ[k] W) = T := congrArg Subtype.val hb
  have ha' : a • (v₀ : V →ₗ[k] W) = CG := congrArg Subtype.val ha
  rw [← hb', ← ha', smul_smul, div_mul_cancel₀ _ ha0]

/-- **Schur's lemma, multiplicity-one form.** Over an algebraically closed field, the space of
intertwiners between two irreducible representations (the target being finite dimensional)
has rank at most one. -/
