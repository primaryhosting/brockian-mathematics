import Mathlib

/-!
# Ghz 4 Normalized
Category: Quantum Computing
Target: QC.ghz4_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

/-- Computational-basis index type for 4 qubits: bit strings `(b₀, b₁, b₂, b₃)`. -/
abbrev Qubits4 := Fin 2 × Fin 2 × Fin 2 × Fin 2

/-- The all-zeros basis state `|0000⟩`. -/

noncomputable def ket1111 : EuclideanSpace ℂ Qubits4 :=
  EuclideanSpace.single (1, 1, 1, 1) 1

/-- The 4-qubit GHZ state `(|0000⟩ + |1111⟩)/√2`. -/
