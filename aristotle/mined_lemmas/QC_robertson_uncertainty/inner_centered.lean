import Mathlib

/-!
# Robertson Uncertainty
Category: Quantum Computing
Target: QC.robertson_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped InnerProductSpace

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QC

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The expectation value of a symmetric operator in a unit state is real. -/

lemma inner_centered (A B : H →ₗ[ℂ] H)
    (hA : ∀ x y : H, ⟪A x, y⟫_ℂ = ⟪x, A y⟫_ℂ)
    (ψ : H) (hψ : ‖ψ‖ = 1) :
    ⟪A ψ - ⟪ψ, A ψ⟫_ℂ • ψ, B ψ - ⟪ψ, B ψ⟫_ℂ • ψ⟫_ℂ
      = ⟪ψ, A (B ψ)⟫_ℂ - ⟪ψ, A ψ⟫_ℂ * ⟪ψ, B ψ⟫_ℂ := by
  have hnorm : ⟪ψ, ψ⟫_ℂ = 1 := by
    have := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) ψ
    rw [this, hψ]
    norm_num
  have hAself : (starRingEnd ℂ) ⟪ψ, A ψ⟫_ℂ = ⟪ψ, A ψ⟫_ℂ := expectation_conj A hA ψ
  have hAψψ : ⟪A ψ, ψ⟫_ℂ = ⟪ψ, A ψ⟫_ℂ := hA ψ ψ
  have hAB : ⟪A ψ, B ψ⟫_ℂ = ⟪ψ, A (B ψ)⟫_ℂ := hA ψ (B ψ)
  simp only [inner_smul_left, inner_smul_right, inner_sub_left, inner_sub_right]
  rw [hAB, hAψψ, hnorm, hAself]
  ring

/-- **Robertson uncertainty relation.**  For symmetric (self-adjoint) operators `A`, `B`
on a complex inner product space and a unit vector `ψ`, the product of the standard
deviations `ΔA = ‖(A - ⟨A⟩)ψ‖` and `ΔB = ‖(B - ⟨B⟩)ψ‖` is at least
`½ |⟨ψ, [A,B] ψ⟩|`. -/
