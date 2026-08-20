/-
# Ghz 7 Normalized
Category: Quantum Computing
Target: QC.ghz7_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

/-- Computational basis states of 7 qubits, indexed by bit strings. -/
abbrev Qubits7 := Fin 7 → Bool

/-- The all-zeros bit string `|0000000⟩`. -/

noncomputable def ghz7Amp (x : Qubits7) : ℂ :=
  if x = allZero then ((1 / Real.sqrt 2 : ℝ) : ℂ)
  else if x = allOne then ((1 / Real.sqrt 2 : ℝ) : ℂ) else 0

/-- The 7-qubit GHZ state `(|0…0⟩ + |1…1⟩)/√2` as a vector in the
Hilbert space `ℂ^(2^7)` whose basis is indexed by bit strings. -/
