/-
# Ghz 6 Normalized
Category: Quantum Computing
Target: QC.ghz6_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

/-- The computational basis of a 6-qubit system is indexed by bit strings
`Fin 6 → Fin 2`; states live in the Hilbert space `EuclideanSpace ℂ (Fin 6 → Fin 2)`
(a 64-dimensional complex inner product space). -/
abbrev Qubits6 := EuclideanSpace ℂ (Fin 6 → Fin 2)

/-- The all-zeros bit string `000000`. -/

private lemma allZeros_ne_allOnes : allZeros ≠ allOnes := by
  intro h
  have := congrFun h 0
  simp [allZeros, allOnes] at this

