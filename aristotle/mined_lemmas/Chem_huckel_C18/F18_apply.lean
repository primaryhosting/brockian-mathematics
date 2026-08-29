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

lemma F18_apply (j k : Fin 18) : F18 j k = (zeta18 ^ (k : ℕ)) ^ (j : ℕ) := by
  simp [F18, Matrix.vandermonde, ← pow_mul, mul_comm]

