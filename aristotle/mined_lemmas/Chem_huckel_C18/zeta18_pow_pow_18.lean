/-!
# Huckel C 18
Category: Chemistry
Target: Chem.huckel_C18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Complex Polynomial Matrix SimpleGraph

namespace Chem

/-- The primitive 18-th root of unity `exp (2πi/18)`. -/

lemma zeta18_pow_pow_18 (k : ℕ) : (zeta18 ^ k) ^ 18 = 1 := by
  rw [← pow_mul, mul_comm, pow_mul, zeta18_pow_18, one_pow]

