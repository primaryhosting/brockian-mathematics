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
noncomputable def expect (T : H →ₗ[ℂ] H) (ψ : H) : ℂ := ⟪ψ, T ψ⟫_ℂ

/-- The standard deviation (uncertainty) of the observable `T` in the state `ψ`,
i.e. `‖(T - ⟪T⟫) ψ‖`. -/
noncomputable def Delta (T : H →ₗ[ℂ] H) (ψ : H) : ℝ := ‖T ψ - (expect T ψ) • ψ‖

/-- The commutator `[A, B] = A B - B A` of two observables. -/
noncomputable def commutator (A B : H →ₗ[ℂ] H) : H →ₗ[ℂ] H := A ∘ₗ B - B ∘ₗ A

/-- For a symmetric operator the expectation value is real. -/
lemma expect_conj {A : H →ₗ[ℂ] H} (hA : A.IsSymmetric) (ψ : H) :
    (starRingEnd ℂ) (expect A ψ) = expect A ψ := by
  unfold expect
  rw [inner_conj_symm]
  exact hA ψ ψ

/-- Elementary bound: `‖⟪u, v⟫ - ⟪v, u⟫‖ ≤ 2 ‖u‖ ‖v‖`. -/
lemma norm_inner_sub_inner_le (u v : H) :
    ‖(⟪u, v⟫_ℂ - ⟪v, u⟫_ℂ)‖ ≤ 2 * ‖u‖ * ‖v‖ := by
  have h1 : ‖⟪u, v⟫_ℂ‖ ≤ ‖u‖ * ‖v‖ := norm_inner_le_norm u v
  have h2 : ‖⟪v, u⟫_ℂ‖ ≤ ‖u‖ * ‖v‖ := by
    have := norm_inner_le_norm (𝕜 := ℂ) v u
    calc ‖⟪v, u⟫_ℂ‖ ≤ ‖v‖ * ‖u‖ := this
      _ = ‖u‖ * ‖v‖ := by ring
  calc ‖(⟪u, v⟫_ℂ - ⟪v, u⟫_ℂ)‖ ≤ ‖⟪u, v⟫_ℂ‖ + ‖⟪v, u⟫_ℂ‖ := norm_sub_le _ _
    _ ≤ ‖u‖ * ‖v‖ + ‖u‖ * ‖v‖ := add_le_add h1 h2
    _ = 2 * ‖u‖ * ‖v‖ := by ring

/-- The expectation of the commutator equals `⟪u, v⟫ - ⟪v, u⟫` for the centered vectors
`u = (A - ⟪A⟫) ψ` and `v = (B - ⟪B⟫) ψ`. -/
lemma expect_commutator_eq {A B : H →ₗ[ℂ] H} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {ψ : H} (hψ : ‖ψ‖ = 1) :
    expect (commutator A B) ψ =
      ⟪A ψ - (expect A ψ) • ψ, B ψ - (expect B ψ) • ψ⟫_ℂ -
      ⟪B ψ - (expect B ψ) • ψ, A ψ - (expect A ψ) • ψ⟫_ℂ := by
  set a : ℂ := expect A ψ with ha
  set b : ℂ := expect B ψ with hb
  have hψψ : ⟪ψ, ψ⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hψ]; norm_num
  have hAψψ : ⟪A ψ, ψ⟫_ℂ = a := by rw [ha, expect]; exact hA ψ ψ
  have hBψψ : ⟪B ψ, ψ⟫_ℂ = b := by rw [hb, expect]; exact hB ψ ψ
  have e1 : ⟪A ψ - a • ψ, B ψ - b • ψ⟫_ℂ = ⟪A ψ, B ψ⟫_ℂ - a * b := by
    simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
      hψψ, hAψψ, ha, hb, expect]
    ring
  have e2 : ⟪B ψ - b • ψ, A ψ - a • ψ⟫_ℂ = ⟪B ψ, A ψ⟫_ℂ - b * a := by
    simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
      hψψ, hBψψ, ha, hb, expect]
    ring
  rw [e1, e2]
  have hc : expect (commutator A B) ψ = ⟪A ψ, B ψ⟫_ℂ - ⟪B ψ, A ψ⟫_ℂ := by
    unfold expect commutator
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, inner_sub_right]
    rw [hA ψ (B ψ), hB ψ (A ψ)]
  rw [hc]
  ring

/-- `Delta` is the usual quantum-mechanical standard deviation: for a symmetric observable `A`
and a unit vector `ψ`, `(ΔA)^2 = ⟨A^2⟩ - ⟨A⟩^2`. -/
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
theorem robertson_uncertainty {A B : H →ₗ[ℂ] H} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {ψ : H} (hψ : ‖ψ‖ = 1) :
    Delta A ψ * Delta B ψ ≥ (1 / 2) * ‖expect (commutator A B) ψ‖ := by
  set u : H := A ψ - (expect A ψ) • ψ with hu
  set v : H := B ψ - (expect B ψ) • ψ with hv
  have key : ‖expect (commutator A B) ψ‖ ≤ 2 * ‖u‖ * ‖v‖ := by
    rw [expect_commutator_eq hA hB hψ]
    exact norm_inner_sub_inner_le u v
  have : (1 / 2 : ℝ) * ‖expect (commutator A B) ψ‖ ≤ ‖u‖ * ‖v‖ := by linarith
  simpa [Delta, hu, hv] using this

end QC

