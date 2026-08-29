/-
# Pauli Basis
Category: Quantum Computing
Target: QC.pauli_basis
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Pauli Basis
Category: Quantum Computing
Target: QC.pauli_basis
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open Matrix

/-- The identity Pauli matrix `I`. -/

def paulis : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ := ![pauliI, pauliX, pauliY, pauliZ]

