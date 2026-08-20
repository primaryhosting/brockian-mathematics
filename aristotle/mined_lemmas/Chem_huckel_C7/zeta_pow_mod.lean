import Mathlib
/-!
# Huckel C 7
Category: Chemistry
Target: Chem.huckel_C7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators Real

namespace Chem

open Complex Finset Matrix

/-- A primitive 7-th root of unity. -/

lemma zeta_pow_mod (n : ℕ) : zeta ^ (n % 7) = zeta ^ n := by
  conv_rhs => rw [← Nat.div_add_mod n 7]
  rw [pow_add, pow_mul, zeta_pow_seven, one_pow, one_mul]

/-- The character `j ↦ ζ ^ j` on `Fin 7`. -/
