import Mathlib
/-!
# Qft Unitary 3
Category: Quantum Computing
Target: QC.qft_unitary_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open Complex Matrix

/-- The primitive `8`-th root of unity `ω = exp(2πi/8)` used by the 3-qubit QFT. -/

lemma qftOmega_primitive : IsPrimitiveRoot qftOmega 8 := by
  have h := Complex.isPrimitiveRoot_exp 8 (by norm_num)
  simpa [qftOmega] using h

