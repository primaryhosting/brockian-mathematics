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

theorem YZ_anticomm : Y * Z + Z * Y = 0 := by
  simp [pauli_ext_iff, Y, Z]

/-- `X` and `Z` anticommute. -/
