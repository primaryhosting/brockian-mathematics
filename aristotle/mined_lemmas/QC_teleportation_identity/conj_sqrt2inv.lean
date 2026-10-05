/-
# Teleportation Identity
Category: Quantum Computing
Target: QC.teleportation_identity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 does not allow a `/-!` module docstring before `import`; the header is repeated
-- verbatim as a module docstring immediately after the imports below.)

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

/-!
## Setup

A qubit is a vector in `ℂ²`, which we index by `Bool` (`false = |0⟩`, `true = |1⟩`).
The three qubits of the teleportation protocol are: Alice's unknown input qubit `ψ`,
Alice's half of an EPR pair, and Bob's half of that pair.
-/

/-- The scalar `1/√2`, as a complex number. -/

@[simp] lemma conj_sqrt2inv : (starRingEnd ℂ) sqrt2inv = sqrt2inv := by
  simp [sqrt2inv]

/-- The Pauli `X` (bit-flip) gate. -/
