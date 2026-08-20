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

theorem teleportation_identity_normalized (psi : Qubit) (m₁ m₂ : Fin 2) :
    (2 : ℂ) • corrected psi m₁ m₂ = psi := by
  rw [teleportation_identity, smul_smul]
  norm_num

end QC

