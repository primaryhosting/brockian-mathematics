import Mathlib

/-!
# Swap Test Overlap
Category: Quantum Computing
Target: QC.swap_test_overlap
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Classical

set_option maxHeartbeats 1000000

namespace QC

/-!
## Model

We model the SWAP test on two `n`-level registers together with one ancilla qubit.
A pure state of the whole system is a function

  `Bool × Fin n × Fin n → ℂ`,

the first component indexing the ancilla qubit.

The circuit is: prepare `|0⟩ ⊗ ψ ⊗ φ`, apply a Hadamard gate on the ancilla,
apply a controlled SWAP of the two registers (controlled on the ancilla),
apply a Hadamard gate on the ancilla again, and finally measure the ancilla.
The test *accepts* when the ancilla is measured in the state `|0⟩`.
-/

variable {n : ℕ}

/-- The Hadamard gate acting on the ancilla qubit. -/

def initialState (psi phi : Fin n → ℂ) : Bool × Fin n × Fin n → ℂ :=
  fun p => if p.1 then 0 else psi p.2.1 * phi p.2.2

/-- The state of the system just before the measurement of the ancilla. -/
