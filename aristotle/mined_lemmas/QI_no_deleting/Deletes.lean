/-
# No Deleting
Category: Frontier Qi
Target: QI.no_deleting
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# No Deleting
Category: Frontier Qi
Target: QI.no_deleting
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QI

/-- A qubit, i.e. a vector of the two-dimensional complex Hilbert space, given by its two
amplitudes. -/

def Deletes {α : Type*} [Fintype α] (U : Sys α ≃ₗᵢ[ℂ] Sys α)
    (a : EuclideanSpace ℂ α) (b : EuclideanSpace ℂ (Fin 2)) (a' : EuclideanSpace ℂ α) : Prop :=
  ∀ u : EuclideanSpace ℂ (Fin 2), ‖u‖ = 1 → U (reg3 u u a) = reg3 u b a'

/-- **No-deleting theorem.** There is no unitary operation on two qubits together with an ancilla
register that deletes one of two identical copies of an unknown qubit state, leaving behind a
fixed blank state and a fixed final ancilla state.

Formally: for a nonzero ancilla state `a`, no unitary `U` (a surjective linear isometry of the
composite state space) satisfies `U (u ⊗ u ⊗ a) = u ⊗ b ⊗ a'` for every unit qubit state `u`,
whatever the blank state `b` and the final ancilla state `a'` are. -/
