/-
# Robertson Uncertainty
Category: Quantum Computing
Target: QC.robertson_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Robertson Uncertainty
Category: Quantum Computing
Target: QC.robertson_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped InnerProductSpace

namespace QC

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The expectation value `⟨ψ|A|ψ⟩` of an observable `A` in the state `ψ`. -/

lemma inner_deviation {A B : E →ₗ[ℂ] E} (hA : IsObservable A) (ψ : E) (hψ : ‖ψ‖ = 1) :
    ⟪A ψ - expect A ψ • ψ, B ψ - expect B ψ • ψ⟫_ℂ
      = ⟪ψ, A (B ψ)⟫_ℂ - expect A ψ * expect B ψ := by
  have hself : ⟪ψ, ψ⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hψ]; norm_num
  have hAψ : ⟪A ψ, ψ⟫_ℂ = expect A ψ := by
    rw [hA]; rfl
  have hAB : ⟪A ψ, B ψ⟫_ℂ = ⟪ψ, A (B ψ)⟫_ℂ := by
    rw [← hA, ← inner_conj_symm (A (B ψ)) ψ, ← inner_conj_symm (B ψ) (A ψ)]
    congr 1
    rw [hA]
  rw [inner_sub_sub_self]
  simp only [inner_smul_left, inner_smul_right, hself, hAψ, hAB,
    conj_expect_of_observable hA ψ]
  have : ⟪ψ, B ψ⟫_ℂ = expect B ψ := rfl
  rw [this]
  ring

/-- **Robertson uncertainty relation.** For observables `A`, `B` and a unit state `ψ`,
the product of the uncertainties is at least half the modulus of the expectation of the
commutator: `ΔA · ΔB ≥ ½ |⟨[A,B]⟩|`. -/
