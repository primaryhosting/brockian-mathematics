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

set_option pp.fullNames false
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QC

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The expectation value `⟪ψ, T ψ⟫` of an observable `T` in the state `ψ`. -/

lemma Delta_sq_eq {A : H →ₗ[ℂ] H} (hA : A.IsSymmetric) {ψ : H} (hψ : ‖ψ‖ = 1) :
    ((Delta A ψ : ℝ) : ℂ) ^ 2 = expect (A ∘ₗ A) ψ - (expect A ψ) ^ 2 := by
  set a : ℂ := expect A ψ with ha
  have hψψ : ⟪ψ, ψ⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hψ]; norm_num
  have haR : (starRingEnd ℂ) a = a := expect_conj hA ψ
  have hAψψ : ⟪A ψ, ψ⟫_ℂ = a := by rw [ha, expect]; exact hA ψ ψ
  have hnorm : ((Delta A ψ : ℝ) : ℂ) ^ 2 = ⟪A ψ - a • ψ, A ψ - a • ψ⟫_ℂ := by
    rw [Delta, ← ha, inner_self_eq_norm_sq_to_K]
    push_cast
    ring
  rw [hnorm]
  have hAA : ⟪A ψ, A ψ⟫_ℂ = expect (A ∘ₗ A) ψ := by
    rw [expect]
    simpa using hA ψ (A ψ)
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    hψψ, hAψψ, haR, hAA]
  ring

/-- **Robertson uncertainty relation.**
For symmetric (self-adjoint) observables `A`, `B` and a unit state vector `ψ`, the product of
the uncertainties is at least half the modulus of the expectation of the commutator:
`ΔA · ΔB ≥ ½ |⟨[A,B]⟩|`. -/
