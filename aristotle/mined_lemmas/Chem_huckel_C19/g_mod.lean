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

namespace Chem

open Complex Finset

/-- `g n = exp (2πi n / 19)`, the basic 19-th root of unity raised to `n`. -/

lemma g_mod (n : ℕ) : g (n % 19) = g n := by
  conv_rhs => rw [← Nat.div_add_mod n 19]
  rw [g_add, g_mul_nineteen, one_mul]

/-- The 19-th root of unity attached to an element of `ZMod 19`. -/
