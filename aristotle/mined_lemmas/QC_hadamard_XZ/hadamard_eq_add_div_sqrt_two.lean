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

theorem hadamard_eq_add_div_sqrt_two : H = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ • (X + Z) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [H, X, Z]

/-- Conjugating `X` by the Hadamard gate yields `Z`. -/
