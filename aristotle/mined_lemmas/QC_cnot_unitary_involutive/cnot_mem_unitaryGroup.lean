/-
# Cnot Unitary Involutive
Category: Quantum Computing
Target: QC.cnot_unitary_involutive
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib


namespace QC

open Matrix

/-- The CNOT gate on two qubits, as a `4 × 4` complex matrix in the
computational basis `|00⟩, |01⟩, |10⟩, |11⟩` (first qubit is the control). -/

theorem cnot_mem_unitaryGroup : cnot ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
  obtain ⟨h1, h2, -⟩ := cnot_unitary_involutive
  exact ⟨h1, h2⟩

end QC


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

