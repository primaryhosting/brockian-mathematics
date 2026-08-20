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

def IsSymmetricOp (A : H →ₗ[ℂ] H) : Prop := ∀ u v : H, ⟪A u, v⟫_ℂ = ⟪u, A v⟫_ℂ

/-- The standard deviation (uncertainty) of the observable `A` in the state `ψ`:
the norm of `A ψ` after subtracting its mean value `⟪ψ, A ψ⟫`. -/
