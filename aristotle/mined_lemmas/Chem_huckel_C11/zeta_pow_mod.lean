import Mathlib

/-!
# Huckel C 11
Category: Chemistry
Target: Chem.huckel_C11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Complex Matrix Polynomial Finset

namespace Chem

/-- A primitive 11th root of unity. -/

lemma zeta_pow_mod (n : ℕ) : zeta ^ (n % 11) = zeta ^ n := by
  conv_rhs => rw [← Nat.div_add_mod n 11]
  rw [pow_add, pow_mul, zeta_pow_eleven, one_pow, one_mul]

