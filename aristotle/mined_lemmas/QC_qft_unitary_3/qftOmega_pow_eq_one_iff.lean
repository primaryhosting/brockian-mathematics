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

lemma qftOmega_pow_eq_one_iff (m : ℕ) : qftOmega ^ m = 1 ↔ 8 ∣ m :=
  qftOmega_primitive.pow_eq_one_iff_dvd m

