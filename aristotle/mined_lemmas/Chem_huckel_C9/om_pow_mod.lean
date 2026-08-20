import Mathlib

/-!
# Huckel C 9
Category: Chemistry
Target: Chem.huckel_C9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators Real
open Complex Polynomial

namespace Chem

/-- A primitive 9th root of unity. -/

theorem om_pow_mod (n : ℕ) : om ^ (n % 9) = om ^ n := by
  conv_rhs => rw [← Nat.div_add_mod n 9, pow_add, pow_mul, om_pow_nine, one_pow, one_mul]

