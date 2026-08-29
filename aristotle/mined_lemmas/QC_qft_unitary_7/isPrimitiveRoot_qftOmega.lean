import Mathlib
/-!
# Qft Unitary 7
Category: Quantum Computing
Target: QC.qft_unitary_7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open Complex Matrix Finset

/-- The primitive `N`-th root of unity `exp (2πi/N)` used to build the QFT matrix. -/

lemma isPrimitiveRoot_qftOmega {N : ℕ} (hN : N ≠ 0) : IsPrimitiveRoot (qftOmega N) N := by
  simpa [qftOmega] using Complex.isPrimitiveRoot_exp N hN

