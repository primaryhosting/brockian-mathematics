/-
# Huckel C 17
Category: Chemistry
Target: Chem.huckel_C17
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 17
Category: Chemistry
Target: Chem.huckel_C17
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open SimpleGraph Matrix Polynomial Complex

namespace Chem

/-- The primitive 17-th root of unity `exp(2πi/17)`. -/

lemma zeta17_pow_congr {a b : ℕ} (h : a % 17 = b % 17) : zeta17 ^ a = zeta17 ^ b := by
  have key : ∀ c : ℕ, zeta17 ^ c = zeta17 ^ (c % 17) := by
    intro c
    conv_lhs => rw [← Nat.div_add_mod c 17]
    rw [pow_add, pow_mul, zeta17_pow_seventeen, one_pow, one_mul]
  rw [key a, key b, h]

