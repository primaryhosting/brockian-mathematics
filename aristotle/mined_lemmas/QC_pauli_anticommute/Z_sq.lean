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

theorem Z_sq : Z * Z = 1 := by
  simp [pauli_ext_iff, Z]

/-- `X` and `Y` anticommute. -/
