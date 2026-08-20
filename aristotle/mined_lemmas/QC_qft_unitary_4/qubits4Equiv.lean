/-
# Qft Unitary 4
Category: Quantum Computing
Target: QC.qft_unitary_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Qft Unitary 4
Category: Quantum Computing
Target: QC.qft_unitary_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

/-- A primitive `16`-th root of unity, `exp (2πi/16)`. -/

def qubits4Equiv : (Fin 4 → Fin 2) ≃ Fin 16 :=
  finFunctionFinEquiv.trans (finCongr (by norm_num))

/-- The 4-qubit QFT written directly on the tensor-product computational basis,
indexed by bit strings `Fin 4 → Fin 2`. -/
