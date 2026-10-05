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

lemma star_omegaRoot_zpow (N : ℕ) (d : ℤ) : star (omegaRoot N ^ d) = omegaRoot N ^ (-d) := by
  rw [omegaRoot_zpow, omegaRoot_zpow, Complex.star_def, ← Complex.exp_conj]
  congr 1
  push_cast
  simp [Complex.ext_iff]
  ring

/-- Orthogonality: a full geometric sum of a nontrivial power of a primitive root vanishes. -/
