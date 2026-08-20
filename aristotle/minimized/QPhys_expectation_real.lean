import Mathlib

/-!
# Heisenberg Uncertainty
Category: Quantum Physics
Target: QPhys.heisenberg_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped InnerProductSpace

namespace QPhys

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- A symmetric (formally self-adjoint) linear operator has real expectation values. -/

lemma expectation_real (A : E →ₗ[ℂ] E) (hA : ∀ u v : E, ⟪A u, v⟫_ℂ = ⟪u, A v⟫_ℂ) (ψ : E) :
    (starRingEnd ℂ) ⟪ψ, A ψ⟫_ℂ = ⟪ψ, A ψ⟫_ℂ := by
  rw [inner_conj_symm]
  exact hA ψ ψ

/-- Robertson form of the uncertainty relation, at the level of the two vectors
`u = (A - ⟪A⟫)ψ` and `v = (B - ⟪B⟫)ψ`: the imaginary part of `⟪u, v⟫` is bounded by
the product of the norms. -/
