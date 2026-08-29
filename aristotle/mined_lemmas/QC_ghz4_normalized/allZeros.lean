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

def allZeros : Fin 4 → Fin 2 := fun _ => 0

/-- The all-ones computational basis label `|1111⟩` for four qubits. -/
