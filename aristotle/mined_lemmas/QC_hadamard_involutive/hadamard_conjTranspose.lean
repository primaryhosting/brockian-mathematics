/-
# Hadamard Involutive
Category: Quantum Computing
Target: QC.hadamard_involutive
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

open Matrix Complex

/-- The single-qubit Hadamard gate `H = (1/√2) • !![1, 1; 1, -1]`. -/

theorem hadamard_conjTranspose : hadamard.conjTranspose = hadamard := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hadamard, Matrix.conjTranspose_apply]

/-- The Hadamard gate squares to the identity: `H * H = I`. -/
