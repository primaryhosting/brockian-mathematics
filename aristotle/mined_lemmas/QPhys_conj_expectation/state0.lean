/-
# Heisenberg Uncertainty
Category: Quantum Physics
Target: QPhys.heisenberg_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped InnerProductSpace
open Matrix

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

set_option grind.warning false

namespace QPhys

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The spread (standard deviation) of the observable `A` in the state `psi`:
the norm of `A psi` after subtracting its mean value `⟪psi, A psi⟫ • psi`. -/

def state0 : EuclideanSpace ℂ (Fin 2) := WithLp.toLp 2 ![1, 0]

/-- The hypotheses of `QPhys.heisenberg_uncertainty` are satisfiable with `ℏ ≠ 0`, and the
bound `Δx·Δp ≥ ℏ/2` is sharp: for the Pauli operators on `ℂ²` and the state `e₀`, equality holds
with `ℏ = 2`. -/
