/-
# Hadamard XZ
Category: Quantum Computing
Target: QC.hadamard_XZ
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

open Matrix

/-- The Pauli `X` gate. -/

theorem hadamard_eq_XZ : H = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ • (PauliX + PauliZ) := by
  unfold H PauliX PauliZ
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- `H * X * H = Z`. -/
