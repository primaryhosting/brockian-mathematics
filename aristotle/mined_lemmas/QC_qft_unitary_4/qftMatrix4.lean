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

noncomputable def qftMatrix4 : Matrix (Fin 16) (Fin 16) ℂ :=
  Matrix.of fun i j => omega16 ^ (i.val * j.val) / 4

