import Mathlib

/-!
# Heisenberg Uncertainty
Category: Quantum Physics
Target: QPhys.heisenberg_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped InnerProductSpace

namespace QPhys

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- A symmetric (formally self-adjoint) linear operator has real expectation values. -/

theorem heisenberg_uncertainty' (X P : E →ₗ[ℂ] E) (ψ : E) (hbar : ℝ) (hb : 0 ≤ hbar)
    (hψ : ‖ψ‖ = 1)
    (hX : ∀ u v : E, ⟪X u, v⟫_ℂ = ⟪u, X v⟫_ℂ)
    (hP : ∀ u v : E, ⟪P u, v⟫_ℂ = ⟪u, P v⟫_ℂ)
    (hcomm : X (P ψ) - P (X ψ) = (Complex.I * hbar) • ψ) :
    hbar / 2 ≤ ‖X ψ - ⟪ψ, X ψ⟫_ℂ • ψ‖ * ‖P ψ - ⟪ψ, P ψ⟫_ℂ • ψ‖ := by
  have := heisenberg_uncertainty X P ψ hbar hψ hX hP hcomm
  rwa [abs_of_nonneg hb] at this

end QPhys

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

