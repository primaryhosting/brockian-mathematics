/-
# Ghz 8 Normalized
Category: Quantum Computing
Target: QC.ghz8_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

/-- The state space of 8 qubits: the complex Hilbert space with orthonormal basis indexed by
the computational basis states `Fin 8 → Bool`. -/
abbrev Qubits8 := EuclideanSpace ℂ (Fin 8 → Bool)

/-- The computational basis state `|b⟩` of 8 qubits. -/

noncomputable def basisState (b : Fin 8 → Bool) : Qubits8 := EuclideanSpace.single b 1

/-- The 8-qubit GHZ state `(|0…0⟩ + |1…1⟩)/√2`. -/
