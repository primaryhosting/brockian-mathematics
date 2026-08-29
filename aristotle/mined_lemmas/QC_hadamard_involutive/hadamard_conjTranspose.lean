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

theorem hadamard_conjTranspose : hadamardMatrixᴴ = hadamardMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hadamardMatrix, Matrix.conjTranspose_apply]

/-- The Hadamard gate squares to the identity: `H * H = 1`. -/
