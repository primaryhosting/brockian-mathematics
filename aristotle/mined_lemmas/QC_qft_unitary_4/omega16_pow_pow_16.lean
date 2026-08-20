/-
# Qft Unitary 4
Category: Quantum Computing
Target: QC.qft_unitary_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Qft Unitary 4
Category: Quantum Computing
Target: QC.qft_unitary_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

/-- A primitive `16`-th root of unity, `exp (2πi/16)`. -/

lemma omega16_pow_pow_16 (n : ℕ) : (omega16 ^ n) ^ 16 = 1 := by
  rw [← pow_mul, mul_comm, pow_mul, isPrimitiveRoot_omega16.pow_eq_one, one_pow]

