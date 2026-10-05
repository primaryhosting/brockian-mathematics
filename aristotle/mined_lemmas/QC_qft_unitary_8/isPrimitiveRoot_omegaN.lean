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

lemma isPrimitiveRoot_omegaN {N : ℕ} (hN : 0 < N) : IsPrimitiveRoot (omegaN N) N := by
  have := Complex.isPrimitiveRoot_exp N hN.ne'
  simpa [omegaN, mul_comm, mul_assoc, mul_left_comm] using this

