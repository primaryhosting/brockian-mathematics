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

lemma expectation_conj (A : H →ₗ[ℂ] H) (hA : ∀ x y : H, ⟪A x, y⟫_ℂ = ⟪x, A y⟫_ℂ) (ψ : H) :
    (starRingEnd ℂ) ⟪ψ, A ψ⟫_ℂ = ⟪ψ, A ψ⟫_ℂ := by
  rw [← inner_conj_symm (𝕜 := ℂ) (x := ψ) (y := A ψ)]
  simp [hA ψ ψ]

/-- The inner product of the two centered vectors. -/
