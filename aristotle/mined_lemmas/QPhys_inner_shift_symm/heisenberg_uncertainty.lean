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

open scoped InnerProductSpace

namespace QPhys

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The expectation value of an observable `A` in the state `ψ`, i.e. the real part of
`⟪ψ, A ψ⟫` (which is automatically real for a symmetric `A` and a unit vector `ψ`). -/

theorem heisenberg_uncertainty (X P : H →ₗ[ℂ] H)
    (hX : ∀ u v : H, ⟪X u, v⟫_ℂ = ⟪u, X v⟫_ℂ)
    (hP : ∀ u v : H, ⟪P u, v⟫_ℂ = ⟪u, P v⟫_ℂ)
    (ψ : H) (hψ : ‖ψ‖ = 1) (ℏ : ℝ)
    (hcomm : X (P ψ) - P (X ψ) = (Complex.I * ℏ) • ψ) :
    uncertainty X ψ * uncertainty P ψ ≥ ℏ / 2 :=
  heisenberg_uncertainty_shift X P hX hP ψ hψ ℏ (expectation X ψ) (expectation P ψ) hcomm

end QPhys

