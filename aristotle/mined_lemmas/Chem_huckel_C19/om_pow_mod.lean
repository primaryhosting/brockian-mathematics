/-
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open Complex (I)
open Matrix

namespace Chem

/-- The primitive 19-th root of unity `exp (2πi/19)`. -/

theorem om_pow_mod (m : ℕ) : om ^ (m % 19) = om ^ m := by
  conv_rhs => rw [← Nat.div_add_mod m 19]
  rw [pow_add, pow_mul, om_pow_19, one_pow, one_mul]

