/-
# Huckel C 16
Category: Chemistry
Target: Chem.huckel_C16
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Matrix Complex

/-- A primitive 16-th root of unity. -/

lemma node16_pow_16 (k : Fin 16) : node16 k ^ 16 = 1 := by
  rw [node16, ← pow_mul, mul_comm, pow_mul, zeta16_pow_16, one_pow]

