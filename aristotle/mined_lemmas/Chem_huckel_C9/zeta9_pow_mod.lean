import Mathlib

/-!
# Huckel C 9
Category: Chemistry
Target: Chem.huckel_C9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Finset

/-- A primitive ninth root of unity. -/

lemma zeta9_pow_mod (n : ℕ) : zeta9 ^ (n % 9) = zeta9 ^ n := by
  conv_rhs => rw [← Nat.div_add_mod n 9]
  rw [pow_add, pow_mul, zeta9_pow_nine, one_pow, one_mul]

