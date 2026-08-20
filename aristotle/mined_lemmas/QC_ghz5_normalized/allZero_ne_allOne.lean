/-
# Ghz 5 Normalized
Category: Quantum Computing
Target: QC.ghz5_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Ghz 5 Normalized
Category: Quantum Computing
Target: QC.ghz5_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(The header block is repeated above as a plain comment because Lean requires
`import` commands to precede any module docstring.)
-/

namespace QC

/-- Computational basis labels for five qubits: bitstrings of length `5`. -/
abbrev Q5 := Fin 5 → Bool

/-- The all-zeros bitstring, labelling `|00000⟩`. -/

theorem allZero_ne_allOne : (allZero : Q5) ≠ allOne := by
  intro h
  have := congrFun h 0
  simp [allZero, allOne] at this

/-- The 5-qubit GHZ state is a unit vector. -/
