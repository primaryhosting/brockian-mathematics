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
noncomputable def expect (A : H →L[ℂ] H) (psi : H) : ℂ := ⟪psi, A psi⟫_ℂ

/-- The uncertainty (standard deviation) `ΔA = ‖(A - ⟨A⟩) ψ‖` of an observable `A`
in the state `ψ`. -/
noncomputable def stdDev (A : H →L[ℂ] H) (psi : H) : ℝ :=
  ‖A psi - (expect A psi) • psi‖

/-- The commutator `[A, B] = A B - B A`. -/
noncomputable def commutator (A B : H →L[ℂ] H) : H →L[ℂ] H := A ∘L B - B ∘L A

/-- A self-adjoint operator is symmetric for the inner product. -/
theorem inner_isSelfAdjoint_left {A : H →L[ℂ] H} (hA : IsSelfAdjoint A) (x y : H) :
    ⟪A x, y⟫_ℂ = ⟪x, A y⟫_ℂ := by
  conv_lhs => rw [show A = ContinuousLinearMap.adjoint A from by
    rw [← ContinuousLinearMap.star_eq_adjoint, hA.star_eq]]
  exact ContinuousLinearMap.adjoint_inner_left A y x

/-- Expectation values of self-adjoint operators are real. -/
theorem conj_expect {A : H →L[ℂ] H} (hA : IsSelfAdjoint A) (psi : H) :
    starRingEnd ℂ (expect A psi) = expect A psi := by
  rw [expect, inner_conj_symm, inner_isSelfAdjoint_left hA]

/-- The uncertainty is the usual standard deviation: `(ΔA)² = ⟨A²⟩ - ⟨A⟩²`. -/
theorem stdDev_sq {A : H →L[ℂ] H} (hA : IsSelfAdjoint A) {psi : H} (hpsi : ‖psi‖ = 1) :
    (stdDev A psi) ^ 2 = (expect (A ∘L A) psi).re - ((expect A psi).re) ^ 2 := by
  have hself : ⟪psi, psi⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hpsi]; norm_num
  have hAs : ⟪A psi, psi⟫_ℂ = expect A psi := by
    rw [inner_isSelfAdjoint_left hA]; rfl
  have hEA : ⟪psi, A psi⟫_ℂ = expect A psi := rfl
  have hca := conj_expect hA psi
  have him : (expect A psi).im = 0 := Complex.conj_eq_iff_im.mp hca
  have hAA : ⟪A psi, A psi⟫_ℂ = expect (A ∘L A) psi := by
    rw [inner_isSelfAdjoint_left hA]; rfl
  set u : H := A psi - (expect A psi) • psi with hu
  have hexp : ⟪u, u⟫_ℂ = expect (A ∘L A) psi - (expect A psi) ^ 2 := by
    rw [hu]
    simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
      hself, hAs, hEA, hAA, hca]
    ring
  have h2 : (⟪u, u⟫_ℂ).re = ‖u‖ ^ 2 := by
    simpa using inner_self_eq_norm_sq (𝕜 := ℂ) u
  rw [stdDev, ← hu, ← h2, hexp]
  simp [Complex.sub_re, pow_two, Complex.mul_re, him]

/-- The commutator expectation is the difference of the two inner products of the
centered vectors. -/
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
theorem robertson_uncertainty {A B : H →L[ℂ] H} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {psi : H} (hpsi : ‖psi‖ = 1) :
    stdDev A psi * stdDev B psi ≥ (1 / 2) * ‖expect (commutator A B) psi‖ := by
  set u : H := A psi - (expect A psi) • psi with hu
  set v : H := B psi - (expect B psi) • psi with hv
  have key : expect (commutator A B) psi = ⟪u, v⟫_ℂ - ⟪v, u⟫_ℂ :=
    expect_commutator_eq hA hB hpsi
  have hswap : ⟪v, u⟫_ℂ = starRingEnd ℂ ⟪u, v⟫_ℂ := (inner_conj_symm v u).symm
  have hnorm : ‖expect (commutator A B) psi‖ = 2 * |(⟪u, v⟫_ℂ).im| := by
    rw [key, hswap]
    rw [Complex.sub_conj]
    simp
  have him : |(⟪u, v⟫_ℂ).im| ≤ ‖⟪u, v⟫_ℂ‖ := Complex.abs_im_le_norm _
  have hcs : ‖⟪u, v⟫_ℂ‖ ≤ ‖u‖ * ‖v‖ := norm_inner_le_norm u v
  have : ‖expect (commutator A B) psi‖ ≤ 2 * (‖u‖ * ‖v‖) := by
    rw [hnorm]
    linarith
  simp only [stdDev, ge_iff_le, ← hu, ← hv]
  linarith
end QC

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

