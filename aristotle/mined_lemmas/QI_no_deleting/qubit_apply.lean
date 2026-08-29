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

@[simp] lemma qubit_apply (x y : ℂ) (i : Fin 2) : qubit x y i = ![x, y] i := rfl

/-- The state space of two qubits together with an ancilla register indexed by `α`. -/
abbrev Sys (α : Type*) := EuclideanSpace ℂ (Fin 2 × Fin 2 × α)

/-- The product (tensor) state `u ⊗ v ⊗ a` of two qubits and an ancilla state. -/
