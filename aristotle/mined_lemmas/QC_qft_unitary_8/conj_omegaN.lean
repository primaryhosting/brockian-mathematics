import Mathlib
/-!
# Qft Unitary 8
Category: Quantum Computing
Target: QC.qft_unitary_8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators Real

namespace QC

open Complex Matrix Finset

/-- The primitive `N`-th root of unity `exp (2 π i / N)`. -/

lemma conj_omegaN (N : ℕ) : (starRingEnd ℂ) (omegaN N) = (omegaN N)⁻¹ := by
  rw [omegaN, ← Complex.exp_conj, ← Complex.exp_neg]
  congr 1
  simp [Complex.ext_iff]
  ring

