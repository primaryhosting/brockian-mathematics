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

theorem qft_conjTranspose_mul_self_4 : qftMatrix4.conjTranspose * qftMatrix4 = 1 :=
  (Matrix.mem_unitaryGroup_iff'.mp qft_unitary_4)

/-- The identification of the 4-qubit computational basis `Fin 4 → Fin 2` (bit strings)
with `Fin 16`, via binary expansion. -/
