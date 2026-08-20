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

def allOne : Q5 := fun _ => true

/-- The 5-qubit GHZ state `(|00000⟩ + |11111⟩)/√2`, as a vector of the
Hilbert space `ℂ^(2^5)` indexed by length-5 bitstrings. -/
