/-!
# Huckel C 15
Category: Chemistry
Target: Chem.huckel_C15
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Finset

/-- A primitive 15-th root of unity. -/

lemma zeta_pow_mod (m : ℕ) : zeta ^ (m % 15) = zeta ^ m := by
  conv_rhs => rw [← Nat.div_add_mod m 15]
  rw [pow_add, pow_mul, zeta_pow_15, one_pow, one_mul]

/-- The character `a ↦ exp (2 π i a / 15)` on `ZMod 15`. -/
