/-
# Huckel C 16
Category: Chemistry
Target: Chem.huckel_C16
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators Real

namespace Chem

open Complex Finset

/-- A primitive 16-th root of unity. -/

lemma zeta_natCast_mul (n : ℕ) (b : ZMod 16) : zeta ((n : ZMod 16) * b) = zeta b ^ n := by
  induction n with
  | zero => simp [zeta_zero]
  | succ n ih =>
      push_cast
      rw [add_mul, one_mul, zeta_add, ih, pow_succ, mul_comm]

