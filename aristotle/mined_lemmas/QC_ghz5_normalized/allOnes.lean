/-
# Ghz 5 Normalized
Category: Quantum Computing
Target: QC.ghz5_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

/-- Computational basis states of a 5-qubit register are indexed by `Fin 5 → Bool`. -/
abbrev Qubits5 := Fin 5 → Bool

/-- The all-zeros bit string `|00000⟩`. -/

def allOnes : Qubits5 := fun _ => true

/-- The 5-qubit GHZ state `(|00000⟩ + |11111⟩)/√2`, as a vector in the
Hilbert space `ℂ^(2^5)` indexed by bit strings. -/
