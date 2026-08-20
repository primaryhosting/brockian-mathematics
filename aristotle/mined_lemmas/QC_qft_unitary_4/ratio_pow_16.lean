import Mathlib

/-!
# Qft Unitary 4
Category: Quantum Computing
Target: QC.qft_unitary_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open Complex Matrix

/-- The primitive `16`-th root of unity `e^{2πi/16}` used by the 4-qubit QFT
(`N = 2^4 = 16`). -/

lemma ratio_pow_16 (k l : Fin 16) :
    (omega16 ^ (k : ℕ) * (omega16 ^ (l : ℕ))⁻¹) ^ 16 = 1 := by
  rw [mul_pow, ← pow_mul, ← inv_pow, ← pow_mul]
  rw [mul_comm (k : ℕ) 16, mul_comm (l : ℕ) 16, pow_mul, pow_mul, omega16_pow_16]
  simp [omega16_pow_16]

/-- The ratio equals `1` exactly when the two indices coincide. -/
