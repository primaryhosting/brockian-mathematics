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

theorem om_pow_pow_nine (t : ℕ) : (om ^ t) ^ 9 = 1 := by
  rw [← pow_mul, mul_comm, pow_mul, om_pow_nine, one_pow]

/-- Orthogonality relation for the 9th roots of unity. -/
