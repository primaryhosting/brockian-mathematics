import Mathlib

/-!
# Ghz 6 Normalized
Category: Quantum Computing
Target: QC.ghz6_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

/-- Computational basis states of 6 qubits, indexed by bit strings `Fin 6 → Bool`. -/
abbrev Qubits6 := Fin 6 → Bool

/-- The 6-qubit GHZ state `(|000000⟩ + |111111⟩)/√2`, as a vector in the
Hilbert space `EuclideanSpace ℂ (Fin 6 → Bool)`. -/

lemma allFalse_ne_allTrue : (fun _ => false : Qubits6) ≠ (fun _ => true) := by
  intro h
  simpa using congrFun h 0

/-- `ghz6` really is the superposition `(|000000⟩ + |111111⟩)/√2` of the two
computational basis vectors. -/
