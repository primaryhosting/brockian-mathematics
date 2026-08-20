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

theorem XY_anticomm : X * Y + Y * X = 0 := by
  simp [pauli_ext_iff, X, Y]

/-- `Y` and `Z` anticommute. -/
