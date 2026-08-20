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

theorem XZ_anticomm : X * Z + Z * X = 0 := by
  simp [pauli_ext_iff, X, Z]

/-- The Pauli matrices `X`, `Y`, `Z` pairwise anticommute, and each squares to the
identity matrix. -/
