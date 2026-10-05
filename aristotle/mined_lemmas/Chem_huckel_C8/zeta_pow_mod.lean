/-
# Huckel C 8
Category: Chemistry
Target: Chem.huckel_C8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Classical

set_option maxHeartbeats 4000000

namespace Chem

/-- A primitive 8-th root of unity. -/

lemma zeta_pow_mod (a b : ℕ) (h : a % 8 = b % 8) : zeta ^ a = zeta ^ b := by
  conv_lhs => rw [← Nat.div_add_mod a 8, pow_add, pow_mul, zeta_pow_eight, one_pow, one_mul, h]
  conv_rhs => rw [← Nat.div_add_mod b 8, pow_add, pow_mul, zeta_pow_eight, one_pow, one_mul]

