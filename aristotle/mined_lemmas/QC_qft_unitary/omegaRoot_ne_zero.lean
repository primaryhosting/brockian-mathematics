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

lemma omegaRoot_ne_zero (N : ℕ) : omegaRoot N ≠ 0 := Complex.exp_ne_zero _

