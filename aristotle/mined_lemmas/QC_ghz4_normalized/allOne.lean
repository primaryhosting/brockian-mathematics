/-
# Ghz 4 Normalized
Category: Quantum Computing
Target: QC.ghz4_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Ghz 4 Normalized
Category: Quantum Computing
Target: QC.ghz4_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open scoped ComplexConjugate

/-- Computational basis states of 4 qubits, indexed by bit strings `Fin 4 → Fin 2`. -/
abbrev Qubits4 := Fin 4 → Fin 2

/-- The all-zeros bit string `|0000⟩`. -/

def allOne : Qubits4 := fun _ => 1

/-- The 4-qubit GHZ state `(|0000⟩ + |1111⟩)/√2`, as a vector in the
16-dimensional complex Hilbert space `EuclideanSpace ℂ (Fin 4 → Fin 2)`. -/
