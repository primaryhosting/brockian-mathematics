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

def allZeros : Qubits5 := fun _ => false

/-- The all-ones bit string `|11111⟩`. -/
