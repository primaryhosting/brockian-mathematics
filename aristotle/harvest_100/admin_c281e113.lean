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
noncomputable def expect (A : E →ₗ[ℂ] E) (ψ : E) : ℂ := ⟪ψ, A ψ⟫_ℂ

/-- The uncertainty (standard deviation) `ΔA = ‖(A - ⟨A⟩) ψ‖` of `A` in the state `ψ`. -/
noncomputable def uncertainty (A : E →ₗ[ℂ] E) (ψ : E) : ℝ := ‖A ψ - expect A ψ • ψ‖

/-- The commutator `[A, B] = AB - BA`. -/
noncomputable def commutator (A B : E →ₗ[ℂ] E) : E →ₗ[ℂ] E := A ∘ₗ B - B ∘ₗ A

/-- An operator is an observable if it is symmetric (self-adjoint) for the inner product. -/
def IsObservable (A : E →ₗ[ℂ] E) : Prop := ∀ x y : E, ⟪A x, y⟫_ℂ = ⟪x, A y⟫_ℂ

/-- The expectation value of an observable is real. -/
lemma conj_expect_of_observable {A : E →ₗ[ℂ] E} (hA : IsObservable A) (ψ : E) :
    (starRingEnd ℂ) (expect A ψ) = expect A ψ := by
  unfold expect
  rw [inner_conj_symm, hA]

/-- The inner product of the two deviation vectors, expressed via `⟪ψ, A (B ψ)⟫`. -/
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
theorem robertson_uncertainty {A B : E →ₗ[ℂ] E}
    (hA : IsObservable A) (hB : IsObservable B) (ψ : E) (hψ : ‖ψ‖ = 1) :
    uncertainty A ψ * uncertainty B ψ ≥ ‖expect (commutator A B) ψ‖ / 2 := by
  set a : E := A ψ - expect A ψ • ψ with ha
  set b : E := B ψ - expect B ψ • ψ with hb
  have h1 : ⟪a, b⟫_ℂ = ⟪ψ, A (B ψ)⟫_ℂ - expect A ψ * expect B ψ :=
    inner_deviation hA ψ hψ
  have h2 : ⟪b, a⟫_ℂ = ⟪ψ, B (A ψ)⟫_ℂ - expect B ψ * expect A ψ :=
    inner_deviation hB ψ hψ
  have hcomm : expect (commutator A B) ψ = ⟪a, b⟫_ℂ - ⟪b, a⟫_ℂ := by
    rw [h1, h2]
    simp only [expect, commutator, LinearMap.sub_apply, LinearMap.comp_apply, inner_sub_right]
    ring
  have hconj : ⟪b, a⟫_ℂ = (starRingEnd ℂ) ⟪a, b⟫_ℂ := (inner_conj_symm a b).symm
  have hbound : ‖expect (commutator A B) ψ‖ ≤ 2 * ‖⟪a, b⟫_ℂ‖ := by
    rw [hcomm, hconj]
    calc ‖⟪a, b⟫_ℂ - (starRingEnd ℂ) ⟪a, b⟫_ℂ‖
        ≤ ‖⟪a, b⟫_ℂ‖ + ‖(starRingEnd ℂ) ⟪a, b⟫_ℂ‖ := norm_sub_le _ _
      _ = 2 * ‖⟪a, b⟫_ℂ‖ := by rw [RCLike.norm_conj]; ring
  have hcs : ‖⟪a, b⟫_ℂ‖ ≤ ‖a‖ * ‖b‖ := norm_inner_le_norm a b
  have : ‖expect (commutator A B) ψ‖ ≤ 2 * (uncertainty A ψ * uncertainty B ψ) := by
    unfold uncertainty
    rw [← ha, ← hb]
    linarith
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

