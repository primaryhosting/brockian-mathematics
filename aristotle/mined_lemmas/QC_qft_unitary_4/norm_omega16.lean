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

lemma norm_omega16 : ‖omega16‖ = 1 := by simp [omega16, Complex.norm_exp]

