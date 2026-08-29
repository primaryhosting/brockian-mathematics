/-
# Robertson Uncertainty
Category: Quantum Computing
Target: QC.robertson_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QC

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The expectation value `⟨A⟩_ψ = ⟪ψ, A ψ⟫` of an operator `A` in the state `ψ`. -/

theorem inner_sub_inner_eq_expect_commutator
    (A B : Module.End ℂ E) (hA : IsSymmetricOp A) (hB : IsSymmetricOp B)
    (ψ : E) (hψ : ‖ψ‖ = 1) :
    inner ℂ (A ψ - expect A ψ • ψ) (B ψ - expect B ψ • ψ)
      - inner ℂ (B ψ - expect B ψ • ψ) (A ψ - expect A ψ • ψ)
      = expect ⁅A, B⁆ ψ := by
  have hnn : (inner ℂ ψ ψ : ℂ) = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hψ]
    norm_num
  have hAψ : inner ℂ (A ψ) ψ = expect A ψ := by
    rw [hA]; rfl
  have hBψ : inner ℂ (B ψ) ψ = expect B ψ := by
    rw [hB]; rfl
  have hcA := conj_expect A hA ψ
  have hcB := conj_expect B hB ψ
  have hcomm : inner ℂ ψ (⁅A, B⁆ ψ) = inner ℂ (A ψ) (B ψ) - inner ℂ (B ψ) (A ψ) := by
    have h1 : (⁅A, B⁆ : Module.End ℂ E) ψ = A (B ψ) - B (A ψ) := by
      simp [Ring.lie_def]
    rw [h1, inner_sub_right, ← hA ψ (B ψ), ← hB ψ (A ψ)]
  show inner ℂ (A ψ - expect A ψ • ψ) (B ψ - expect B ψ • ψ)
      - inner ℂ (B ψ - expect B ψ • ψ) (A ψ - expect A ψ • ψ)
      = inner ℂ ψ (⁅A, B⁆ ψ)
  rw [hcomm]
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    hnn, hAψ, hBψ, hcA, hcB, show inner ℂ ψ (A ψ) = expect A ψ from rfl,
    show inner ℂ ψ (B ψ) = expect B ψ from rfl]
  ring

/-- **Robertson uncertainty relation.**  For symmetric (self-adjoint) observables `A`, `B`
and a unit state vector `ψ`, the product of the uncertainties is at least one half the
modulus of the expectation value of the commutator:
`ΔA · ΔB ≥ ½ |⟨[A, B]⟩|`. -/
