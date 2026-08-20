/-
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Polynomial Matrix Complex SimpleGraph Finset

namespace Chem

/-- The primitive 19-th root of unity `exp (2πi/19)`. -/

lemma zeta_pow_mod (m : ℕ) : zeta ^ (m % 19) = zeta ^ m := by
  conv_rhs => rw [← Nat.div_add_mod m 19]
  rw [pow_add, pow_mul, zeta_pow_19, one_pow, one_mul]

