import Mathlib

/-!
# Ghz 4 Normalized
Category: Quantum Computing
Target: QC.ghz4_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

/-- The computational basis of a 4-qubit system is indexed by bit strings `Fin 4 → Bool`. -/
abbrev Qubits4 := Fin 4 → Bool

/-- The all-zeros bit string, i.e. the basis label of `|0000⟩`. -/

lemma ghz4_eq_zero {x : Qubits4} (h0 : x ≠ allZero) (h1 : x ≠ allOne) : ghz4.ofLp x = 0 := by
  simp [ghz4, h0, h1]

