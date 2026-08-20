import Mathlib
/-!
# Huckel C 13
Category: Chemistry
Target: Chem.huckel_C13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real
open Complex Matrix

namespace Chem

/-- A primitive 13-th root of unity. -/

lemma omega13_pow_mod (n : ℕ) : omega13 ^ (n % 13) = omega13 ^ n := by
  conv_rhs => rw [← Nat.div_add_mod n 13]
  rw [pow_add, pow_mul, omega13_pow_13, one_pow, one_mul]

