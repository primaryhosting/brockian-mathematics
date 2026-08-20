import Mathlib

/-!
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix Finset Complex

set_option maxHeartbeats 1000000

namespace Chem

/-- A primitive 14-th root of unity. -/

lemma chi_pow_14 (m : Fin 14) : (chi m) ^ 14 = 1 := by
  rw [chi, ← pow_mul, mul_comm, pow_mul, om_pow_14, one_pow]

