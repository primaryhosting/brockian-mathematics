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

noncomputable def ket1 : Qubits8 := EuclideanSpace.single (fun _ => true) 1

/-- The 8-qubit GHZ state `(|0…0⟩ + |1…1⟩)/√2`. -/
