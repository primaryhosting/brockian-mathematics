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

lemma omegaRoot_zpow (N : ℕ) (d : ℤ) :
    omegaRoot N ^ d = Complex.exp (d * (2 * Real.pi * Complex.I / N)) := by
  rw [omegaRoot, ← Complex.exp_int_mul]

