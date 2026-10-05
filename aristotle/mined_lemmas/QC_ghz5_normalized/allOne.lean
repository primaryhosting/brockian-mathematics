/-!
# Ghz 5 Normalized
Category: Quantum Computing
Target: QC.ghz5_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

/-- Computational basis labels for 5 qubits: functions `Fin 5 → Bool`
(so the state space `EuclideanSpace ℂ (Fin 5 → Bool)` is the 32-dimensional
tensor product of five qubit spaces). -/
abbrev Qubits5 := Fin 5 → Bool

/-- The all-zeros label `|00000⟩`. -/

def allOne : Qubits5 := fun _ => true

