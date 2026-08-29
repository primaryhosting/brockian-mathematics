import Mathlib

/-!
# Huckel C 12
Category: Chemistry
Target: Chem.huckel_C12
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real

set_option maxHeartbeats 1000000

namespace Chem

open Complex Polynomial Matrix Finset

/-- The primitive 12-th root of unity `exp(2πi/12)`. -/

lemma w12_pow_mod (n : ℕ) : w12 ^ (n % 12) = w12 ^ n := by
  conv_rhs => rw [← Nat.div_add_mod n 12]
  rw [pow_add, pow_mul, w12_pow_twelve, one_pow, one_mul]

