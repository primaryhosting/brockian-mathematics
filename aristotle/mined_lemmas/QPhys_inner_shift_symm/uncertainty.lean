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

noncomputable def uncertainty (A : H →ₗ[ℂ] H) (ψ : H) : ℝ :=
  ‖A ψ - (expectation A ψ : ℂ) • ψ‖

/-- For a symmetric operator `A`, a real scalar `a` and any vectors `ψ, v`,
`⟪A ψ - a • ψ, v⟫ = ⟪ψ, A v - a • v⟫`. -/
