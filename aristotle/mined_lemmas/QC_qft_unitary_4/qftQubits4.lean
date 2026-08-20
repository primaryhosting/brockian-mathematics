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

noncomputable def qftQubits4 : Matrix (Fin 4 → Fin 2) (Fin 4 → Fin 2) ℂ :=
  qftMatrix4.submatrix qubits4Equiv qubits4Equiv

/-- The 4-qubit QFT, indexed by the computational basis of bit strings, is unitary. -/
