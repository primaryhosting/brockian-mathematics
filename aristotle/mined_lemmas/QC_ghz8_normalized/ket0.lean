/-
# Ghz 8 Normalized
Category: Quantum Computing
Target: QC.ghz8_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

/-- The state space of 8 qubits: the Hilbert space `ℂ^(2^8)`, indexed by the
computational basis states `Fin 8 → Bool`. -/
abbrev Qubits8 : Type := EuclideanSpace ℂ (Fin 8 → Bool)

/-- The all-zeros computational basis state `|0…0⟩`. -/

noncomputable def ket0 : Qubits8 := EuclideanSpace.single (fun _ => false) 1

/-- The all-ones computational basis state `|1…1⟩`. -/
