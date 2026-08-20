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

/-
# Heisenberg Uncertainty
Category: Quantum Physics
Target: QPhys.heisenberg_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Heisenberg Uncertainty
Category: Quantum Physics
Target: QPhys.heisenberg_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


namespace QPhys

open scoped InnerProductSpace ComplexConjugate

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A (bounded, everywhere-defined) linear operator on a complex inner product space is
*symmetric* if it satisfies `⟪A u, v⟫ = ⟪u, A v⟫` for all vectors `u`, `v`. -/

theorem heisenberg_uncertainty_of_ccr {X P : H →ₗ[ℂ] H} (hbar : ℝ)
    (hX : IsSymmetricOp X) (hP : IsSymmetricOp P)
    (hccr : ∀ φ : H, X (P φ) - P (X φ) = (Complex.I * hbar) • φ)
    {ψ : H} (hψ : ‖ψ‖ = 1) :
    spread X ψ * spread P ψ ≥ hbar / 2 := by
  refine heisenberg_uncertainty hbar hX hP hψ ?_
  have hself : ⟪ψ, ψ⟫_ℂ = 1 := by simp [inner_self_eq_norm_sq_to_K, hψ]
  rw [hccr ψ, inner_smul_right, hself, mul_one]

/-- The squared (variance) form of the uncertainty principle: `(Δx)² (Δp)² ≥ ℏ² / 4`. -/
