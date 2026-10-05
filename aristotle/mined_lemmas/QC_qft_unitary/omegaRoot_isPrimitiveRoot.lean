import Mathlib

/-!
# Qft Unitary
Category: Quantum Computing
Target: QC.qft_unitary
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open Complex Finset Matrix

/-- The primitive `N`-th root of unity `exp(2πi/N)`. -/

lemma omegaRoot_isPrimitiveRoot {N : ℕ} (hN : N ≠ 0) :
    IsPrimitiveRoot (omegaRoot N) N :=
  Complex.isPrimitiveRoot_exp N hN

