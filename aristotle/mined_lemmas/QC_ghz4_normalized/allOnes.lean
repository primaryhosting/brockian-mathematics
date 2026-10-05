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

/-- The all-zeros computational basis label `|0000⟩` for four qubits. -/

def allOnes : Fin 4 → Fin 2 := fun _ => 1

/-- The 4-qubit GHZ state `(|0000⟩ + |1111⟩)/√2`, as a vector in the
Hilbert space `ℂ^(Fin 4 → Fin 2)` of four qubits. -/
