import Mathlib
/-!
# Robertson Uncertainty
Category: Quantum Computing
Target: QC.robertson_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on the header: Lean 4 requires `import` to be the very first command of a module,
so the mandated header comment is placed immediately after the single `import Mathlib` line.
-/

namespace QC

open scoped ComplexConjugate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The expectation value `⟪ψ, A ψ⟫` of an observable `A` in the state `ψ`. -/

lemma centered_commutator (A B : E →ₗ[ℂ] E) (ψ : E) :
    centered A ψ ∘ₗ centered B ψ - centered B ψ ∘ₗ centered A ψ = A ∘ₗ B - B ∘ₗ A := by
  ext x
  simp only [centered, LinearMap.coe_comp, Function.comp_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, LinearMap.map_sub, LinearMap.map_smul]
  abel_nf
  module

/-- The expectation of the commutator equals `⟪u, v⟫ - ⟪v, u⟫` where `u = (A - ⟨A⟩)ψ`,
`v = (B - ⟨B⟩)ψ`. -/
