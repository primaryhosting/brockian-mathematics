/-
# Huckel C 18
Category: Chemistry
Target: Chem.huckel_C18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 18
Category: Chemistry
Target: Chem.huckel_C18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open Complex

namespace Chem

/-- A primitive 18-th root of unity. -/

theorem om_pow_mod (a : ℕ) : om ^ (a % 18) = om ^ a := by
  conv_rhs => rw [← Nat.div_add_mod a 18]
  rw [pow_add, pow_mul, om_pow_eighteen, one_pow, one_mul]

