import Mathlib

/-!
# Hadamard Involutive
Category: Quantum Computing
Target: QC.hadamard_involutive
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open Matrix

/-- The single-qubit Hadamard gate `H = (1/√2) • !![1, 1; 1, -1]`, as a complex
`2 × 2` matrix. -/

noncomputable def hadamardMatrix : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / Real.sqrt 2 : ℝ) • !![1, 1; 1, -1]

/-- The Hadamard gate is self-adjoint: `Hᴴ = H`. -/
