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

theorem X_sq : X * X = 1 := by
  simp [pauli_ext_iff, X]

/-- `Y * Y = 1`. -/
