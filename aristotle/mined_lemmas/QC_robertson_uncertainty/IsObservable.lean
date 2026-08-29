/-
# Robertson Uncertainty
Category: Quantum Computing
Target: QC.robertson_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped InnerProductSpace ComplexConjugate

namespace QC

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- An *observable* is a symmetric (self-adjoint) linear operator on a complex
inner product space. -/

def IsObservable (A : E →ₗ[ℂ] E) : Prop := ∀ x y, ⟪A x, y⟫_ℂ = ⟪x, A y⟫_ℂ

/-- The expectation value `⟨A⟩ψ = ⟪ψ, A ψ⟫` of an operator `A` in the state `ψ`. -/
