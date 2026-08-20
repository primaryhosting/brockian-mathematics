/-
# Ghz 7 Normalized
Category: Quantum Computing
Target: QC.ghz7_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

/-- The computational basis of a 7-qubit register is indexed by bit strings
`Fin 7 → Bool`; states live in the Hilbert space `EuclideanSpace ℂ (Fin 7 → Bool)`. -/
abbrev Qubits7 := EuclideanSpace ℂ (Fin 7 → Bool)

/-- The all-zeros basis state `|0000000⟩`. -/

private lemma inner_allZeros_allOnes : (inner ℂ allZeros allOnes : ℂ) = 0 := by
  simp [allZeros, allOnes, EuclideanSpace.inner_single_left,
    EuclideanSpace.single_apply, funext_iff]

