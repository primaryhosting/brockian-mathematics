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

lemma inner_commutator_eq {A B : E →ₗ[ℂ] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric) (ψ : E) :
    inner ℂ ψ ((A ∘ₗ B - B ∘ₗ A) ψ)
      = inner ℂ (centered A ψ ψ) (centered B ψ ψ)
        - conj (inner ℂ (centered A ψ ψ) (centered B ψ ψ)) := by
  rw [← centered_commutator A B ψ]
  rw [inner_conj_symm]
  simp only [LinearMap.sub_apply, LinearMap.coe_comp, Function.comp_apply, inner_sub_right]
  rw [← (centered_isSymmetric hA ψ) ψ (centered B ψ ψ),
    ← (centered_isSymmetric hB ψ) ψ (centered A ψ ψ)]

/-- **Robertson uncertainty relation.** For symmetric (self-adjoint) observables `A`, `B`
and any state `ψ`, the product of the uncertainties `ΔA · ΔB` is at least
`½ |⟨[A, B]⟩|`. -/
