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

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames false
set_option pp.structureInstances true
set_option pp.coercions.types false
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QC

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- An operator `A` on a complex inner product space is *symmetric* (an observable) if
`⟪A x, y⟫ = ⟪x, A y⟫` for all `x, y`. -/

lemma stddev_sq (A : H →ₗ[ℂ] H) (hA : IsSymmetricOp A) (ψ : H) (hψ : ‖ψ‖ = 1) :
    ((stddev A ψ : ℂ)) ^ 2 = expect (A ∘ₗ A) ψ - (expect A ψ) ^ 2 := by
  have hnorm : (inner ℂ ψ ψ : ℂ) = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hψ]; norm_num
  have ha : (starRingEnd ℂ) (expect A ψ) = expect A ψ := expect_conj A hA ψ
  have h1 : ((stddev A ψ : ℂ)) ^ 2
      = (inner ℂ (A ψ - expect A ψ • ψ) (A ψ - expect A ψ • ψ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  have h2 : (inner ℂ (A ψ) ψ : ℂ) = expect A ψ := by
    rw [← ha]; unfold expect; rw [inner_conj_symm]
  have h4 : (inner ℂ (A ψ) (A ψ) : ℂ) = expect (A ∘ₗ A) ψ := by
    unfold expect; rw [hA]; rfl
  rw [h1, inner_sub_left, inner_sub_right, inner_sub_right, inner_smul_left, inner_smul_left,
    inner_smul_right, inner_smul_right, h2, hnorm, ha, h4]
  show _ = _
  unfold expect
  ring

/-- **Robertson uncertainty relation.**  For observables (symmetric operators) `A`, `B`
on a complex inner product space and a unit state `ψ`,
`ΔA · ΔB ≥ ½ |⟨[A, B]⟩|`. -/
