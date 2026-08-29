import Mathlib

/-!
# Huckel C 9
Category: Chemistry
Target: Chem.huckel_C9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open SimpleGraph Matrix

namespace Chem

/-- The primitive 9-th root of unity `exp (2πi/9)`. -/

lemma omega9_pow_nine_pow (k : ℕ) : (omega9 ^ k) ^ 9 = 1 := by
  rw [← pow_mul, mul_comm, pow_mul, omega9_pow_nine, one_pow]

/-- `ω^k + ω^{-k} = 2 cos (2πk/9)`. -/
