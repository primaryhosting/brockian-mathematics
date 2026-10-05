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

theorem postMeasurement_eq (psi : Bool → ℂ) (a b : Bool) :
    postMeasurement psi a b =
      ((if b then pauliX else 1) * (if a then pauliZ else 1)).mulVec psi := by
  funext k
  simp only [postMeasurement, totalState, bellBasis, bellPair, pauliX, pauliZ,
    Matrix.mulVec, dotProduct, Matrix.mul_apply, Fintype.sum_bool]
  cases a <;> cases b <;> cases k <;>
    simp [mul_comm, mul_assoc] <;>
    rw [← mul_assoc, sqrt2inv_sq] <;> ring

/-- **Teleportation identity.** For every input qubit `ψ` and every Bell-measurement
outcome `(a, b)`, applying Bob's correction `Z^a X^b` to his post-measurement state
returns exactly the input state `ψ`. -/
