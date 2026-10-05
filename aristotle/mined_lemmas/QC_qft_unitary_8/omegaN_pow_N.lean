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

lemma omegaN_pow_N {N : ℕ} (hN : 0 < N) : omegaN N ^ N = 1 :=
  (isPrimitiveRoot_omegaN hN).pow_eq_one

