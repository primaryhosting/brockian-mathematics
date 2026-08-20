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

noncomputable def ket0000 : EuclideanSpace ℂ Qubits4 :=
  EuclideanSpace.single (0, 0, 0, 0) 1

/-- The all-ones basis state `|1111⟩`. -/
