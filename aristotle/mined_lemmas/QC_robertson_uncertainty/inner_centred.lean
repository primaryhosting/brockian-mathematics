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

lemma inner_centred {A : E →ₗ[ℂ] E} (hA : IsObservable A) (B : E →ₗ[ℂ] E)
    {ψ : E} (hψ : ‖ψ‖ = 1) :
    ⟪A ψ - expect A ψ • ψ, B ψ - expect B ψ • ψ⟫_ℂ
      = ⟪ψ, A (B ψ)⟫_ℂ - expect A ψ * expect B ψ := by
  have hAψ : ⟪A ψ, ψ⟫_ℂ = ⟪ψ, A ψ⟫_ℂ := hA _ _
  have hABψ : ⟪A ψ, B ψ⟫_ℂ = ⟪ψ, A (B ψ)⟫_ℂ := hA _ _
  simp only [expect]
  simp [hAψ, hABψ, hψ]
  ring

/-- **Robertson uncertainty relation.**  For observables `A`, `B` (symmetric linear
operators on a complex inner product space) and a normalized state `ψ`, the product of
the standard deviations is at least half the modulus of the expectation of the
commutator:  `ΔA · ΔB ≥ ½ |⟨[A, B]⟩|`. -/
