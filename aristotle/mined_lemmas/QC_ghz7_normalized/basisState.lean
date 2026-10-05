/-
# Ghz 7 Normalized
Category: Quantum Computing
Target: QC.ghz7_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

/-- The state space of 7 qubits: the complex Hilbert space with orthonormal basis
indexed by the computational basis states `Fin 7 → Bool`. -/
abbrev Qubits7 := EuclideanSpace ℂ (Fin 7 → Bool)

/-- The computational basis state `|b⟩` for a bit string `b : Fin 7 → Bool`. -/

noncomputable def basisState (b : Fin 7 → Bool) : Qubits7 := EuclideanSpace.single b 1

/-- The all-zeros basis state `|0000000⟩`. -/
