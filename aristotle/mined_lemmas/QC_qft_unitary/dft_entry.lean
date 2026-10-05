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

lemma dft_entry (N : ℕ) (j k : Fin N) :
    dftMatrix N j k = (1 / Real.sqrt N : ℝ) * omegaRoot N ^ (((j : ℕ) : ℤ) * ((k : ℕ) : ℤ)) := by
  rw [dftMatrix, omegaRoot_zpow]
  congr 2
  push_cast
  ring

/-- The DFT matrix of any positive size is unitary. -/
