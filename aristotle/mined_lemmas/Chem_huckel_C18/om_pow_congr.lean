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

namespace Chem

open Matrix SimpleGraph Complex

/-- The primitive 18-th root of unity `exp(2πi/18)`. -/

lemma om_pow_congr {a b : ℕ} (h : a % 18 = b % 18) : om ^ a = om ^ b := by
  conv_lhs => rw [← Nat.div_add_mod a 18]
  conv_rhs => rw [← Nat.div_add_mod b 18]
  rw [pow_add, pow_add, pow_mul, pow_mul, om_pow_18, one_pow, one_pow, h]

