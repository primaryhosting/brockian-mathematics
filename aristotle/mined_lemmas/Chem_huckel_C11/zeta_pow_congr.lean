/-
# Huckel C 11
Category: Chemistry
Target: Chem.huckel_C11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Complex Finset

/-- A primitive 11-th root of unity. -/

lemma zeta_pow_congr {a b : ℕ} (h : a % 11 = b % 11) : zeta ^ a = zeta ^ b := by
  have key : ∀ n : ℕ, zeta ^ n = zeta ^ (n % 11) := by
    intro n
    conv_lhs => rw [← Nat.div_add_mod n 11]
    rw [pow_add, pow_mul, zeta_pow_eleven, one_pow, one_mul]
  rw [key a, key b, h]

