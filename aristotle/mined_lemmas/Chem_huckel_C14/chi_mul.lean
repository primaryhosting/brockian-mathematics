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

lemma chi_mul (a b : Fin 14) : chi (a * b) = (chi a) ^ b.val := by
  simp only [chi, Fin.val_mul, pow_mod_14 om om_pow_14, pow_mul]

