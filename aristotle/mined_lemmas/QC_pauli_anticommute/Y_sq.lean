/-
# Pauli Anticommute
Category: Quantum Computing
Target: QC.pauli_anticommute
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

open Matrix

/-- The Pauli `X` matrix. -/

theorem Y_sq : Y * Y = 1 := by
  simp [pauli_ext_iff, Y, Complex.I_mul_I]

/-- `Z * Z = 1`. -/
