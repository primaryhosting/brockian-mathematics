/-!
# Huckel C 18
Category: Chemistry
Target: Chem.huckel_C18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Complex Polynomial Matrix SimpleGraph

namespace Chem

/-- The primitive 18-th root of unity `exp (2πi/18)`. -/

lemma pow_mod18 {u : ℂ} (hu : u ^ 18 = 1) (x : ℕ) : u ^ (x % 18) = u ^ x := by
  conv_rhs => rw [← Nat.div_add_mod x 18]
  rw [pow_add, pow_mul, hu, one_pow, one_mul]

