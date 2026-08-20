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

lemma pow_mod_14 (z : ℂ) (hz : z ^ 14 = 1) (m : ℕ) : z ^ (m % 14) = z ^ m := by
  conv_rhs => rw [← Nat.div_add_mod m 14]
  rw [pow_add, pow_mul, hz, one_pow, one_mul]

