/-
# Ghz 7 Normalized
Category: Quantum Computing
Target: QC.ghz7_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

/-- The state space of `n` qubits, realized as the Hilbert space `ℂ^(2^n)` with
basis vectors indexed by bit strings `Fin n → Fin 2`. -/
abbrev QubitState (n : ℕ) := EuclideanSpace ℂ (Fin n → Fin 2)

/-- The all-zeros bit string `0…0`, indexing the basis vector `|0…0⟩`. -/

def allZeros (n : ℕ) : Fin n → Fin 2 := fun _ => 0

/-- The all-ones bit string `1…1`, indexing the basis vector `|1…1⟩`. -/
