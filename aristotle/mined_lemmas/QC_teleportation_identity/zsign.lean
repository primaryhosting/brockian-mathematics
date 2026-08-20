/-
# Teleportation Identity
Category: Quantum Computing
Target: QC.teleportation_identity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace QC

/-- A one-qubit state is a vector of amplitudes indexed by `Fin 2`. -/
abbrev Qubit := Fin 2 → ℂ

/-- A three-qubit state is an amplitude for each triple of bit values. -/
abbrev Qubit3 := Fin 2 → Fin 2 → Fin 2 → ℂ

/-- `(-1)^(i*k)`, the phase produced by the Pauli-`Z` gate on basis state `k`
raised to the power `i`. -/

noncomputable def zsign (i k : Fin 2) : ℂ := if i = 1 ∧ k = 1 then -1 else 1

/-- The Bell state `(|00⟩ + |11⟩)/√2` of the two qubits shared by Alice and Bob. -/
