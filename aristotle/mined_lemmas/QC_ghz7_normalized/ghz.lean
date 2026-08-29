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

noncomputable def ghz (n : ℕ) : QubitState n :=
  ((Real.sqrt 2 : ℂ))⁻¹ •
    (EuclideanSpace.single (allZeros n) 1 + EuclideanSpace.single (allOnes n) 1)

/-- For at least one qubit, the all-zeros and all-ones bit strings are distinct. -/
