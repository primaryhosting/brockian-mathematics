/-
# Robertson Uncertainty
Category: Quantum Computing
Target: QC.robertson_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped InnerProductSpace

namespace QC

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The expectation value `⟨A⟩ψ = ⟪ψ, A ψ⟫` of an observable `A` in the state `ψ`. -/

theorem expect_commutator_eq {A B : H →L[ℂ] H} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {psi : H} (hpsi : ‖psi‖ = 1) :
    expect (commutator A B) psi
      = ⟪A psi - (expect A psi) • psi, B psi - (expect B psi) • psi⟫_ℂ
        - ⟪B psi - (expect B psi) • psi, A psi - (expect A psi) • psi⟫_ℂ := by
  have hself : ⟪psi, psi⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hpsi]; norm_num
  have hAs : ⟪A psi, psi⟫_ℂ = expect A psi := by
    rw [inner_isSelfAdjoint_left hA]; rfl
  have hBs : ⟪B psi, psi⟫_ℂ = expect B psi := by
    rw [inner_isSelfAdjoint_left hB]; rfl
  have hEA : ⟪psi, A psi⟫_ℂ = expect A psi := rfl
  have hEB : ⟪psi, B psi⟫_ℂ = expect B psi := rfl
  have hca := conj_expect hA psi
  have hcb := conj_expect hB psi
  have hcomm : expect (commutator A B) psi = ⟪A psi, B psi⟫_ℂ - ⟪B psi, A psi⟫_ℂ := by
    simp only [expect, commutator, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.coe_comp', Function.comp_apply, inner_sub_right,
      inner_isSelfAdjoint_left hA, inner_isSelfAdjoint_left hB]
  rw [hcomm]
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    hself, hAs, hBs, hEA, hEB, hca, hcb]
  ring

/-- **Robertson uncertainty relation.**  For self-adjoint observables `A`, `B` and a
normalized state `ψ`, the product of the uncertainties is at least half the modulus of
the expectation value of the commutator:  `ΔA · ΔB ≥ ½ |⟨[A,B]⟩|`. -/
