/-
# Teleportation Identity
Category: Quantum Computing
Target: QC.teleportation_identity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Teleportation Identity
Category: Quantum Computing
Target: QC.teleportation_identity
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

set_option grind.warning false

namespace QC

/-- A single-qubit state is a complex amplitude function on the computational basis
`{|0⟩, |1⟩}`, indexed by `Bool` (`false ↦ |0⟩`, `true ↦ |1⟩`). -/
abbrev Qubit := Bool → ℂ

/-- The scalar `1/√2`, as a complex number. -/

lemma postMeasurement_initialState (psi : Qubit) (m n k : Bool) :
    postMeasurement m n (initialState psi) k =
      (if m && (xor k n) then -(1 / 2 : ℂ) else (1 / 2 : ℂ)) * psi (xor k n) := by
  simp only [postMeasurement, initialState, bellPair, bellBasis, Fintype.sum_bool]
  cases m <;> cases n <;> cases k <;>
    simp <;>
    first
      | linear_combination psi false * invSqrt2_mul_invSqrt2
      | linear_combination psi true * invSqrt2_mul_invSqrt2

/-- Each of the four Bell outcomes occurs with probability `1/4`, independently of the
input state: this is what the renormalization factor `2` in `teleported` accounts for. -/
