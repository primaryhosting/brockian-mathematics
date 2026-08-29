/-
# Huckel C 9
Category: Chemistry
Target: Chem.huckel_C9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 9
Category: Chemistry
Target: Chem.huckel_C9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
open Complex Polynomial SimpleGraph

namespace Chem

/-- A primitive `9`-th root of unity. -/

theorem zeta_pow_mod (n : ℕ) : zeta ^ (n % 9) = zeta ^ n := by
  conv_rhs => rw [← Nat.div_add_mod n 9, pow_add, pow_mul, zeta_pow_nine, one_pow, one_mul]

