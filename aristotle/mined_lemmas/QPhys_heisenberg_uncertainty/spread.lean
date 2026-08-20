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

namespace QPhys

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The spread (standard deviation) of the observable `A` in the state `ψ`:
the norm of `A ψ` after subtracting its expectation value `⟪ψ, A ψ⟫`. -/

noncomputable def spread (A : H →ₗ[ℂ] H) (ψ : H) : ℝ :=
  ‖A ψ - (inner ℂ ψ (A ψ)) • ψ‖

/-- **Heisenberg uncertainty principle.**  If `X` and `P` are symmetric operators on a
complex inner product space satisfying the canonical commutation relation
`X P ψ - P X ψ = i ħ ψ` at a normalized state `ψ`, then the product of the spreads of
`X` and `P` in the state `ψ` is at least `ħ / 2`. -/
