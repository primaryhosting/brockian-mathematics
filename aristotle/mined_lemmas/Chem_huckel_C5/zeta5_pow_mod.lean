/-
# Huckel C 5
Category: Chemistry
Target: Chem.huckel_C5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Huckel C 5
Category: Chemistry
Target: Chem.huckel_C5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset Matrix

namespace Chem

/-- A primitive fifth root of unity. -/

lemma zeta5_pow_mod (x : ℕ) : zeta5 ^ (x % 5) = zeta5 ^ x := by
  conv_rhs => rw [← Nat.div_add_mod x 5]
  rw [pow_add, pow_mul, zeta5_pow_five, one_pow, one_mul]

/-! ### Basic facts about the character `e5` -/

