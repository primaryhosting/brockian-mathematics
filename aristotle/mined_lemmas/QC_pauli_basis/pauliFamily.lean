/-
# Pauli Basis
Category: Quantum Computing
Target: QC.pauli_basis
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

open Matrix

/-- The identity Pauli matrix `I`. -/

def pauliFamily : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ := ![pauliI, pauliX, pauliY, pauliZ]

/-- The Pauli matrices are linearly independent over `ℂ`. -/
