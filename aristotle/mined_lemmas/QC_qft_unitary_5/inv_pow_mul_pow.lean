/-
# Qft Unitary 5
Category: Quantum Computing
Target: QC.qft_unitary_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

open Complex Matrix Finset

/-- The primitive `N`-th root of unity `exp (2πi / N)` used in the QFT. -/

private lemma inv_pow_mul_pow (z : ℂ) (a b c : ℕ) :
    (z⁻¹) ^ (a * b) * z ^ (a * c) = (z ^ c * (z ^ b)⁻¹) ^ a := by
  rw [inv_pow, mul_pow, inv_pow, ← pow_mul, ← pow_mul, mul_comm c a, mul_comm b a, mul_comm]

/-- The `N`-point QFT matrix is unitary, for any `N ≠ 0`. -/
