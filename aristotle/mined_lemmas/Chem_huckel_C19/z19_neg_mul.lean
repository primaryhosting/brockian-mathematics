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

lemma z19_neg_mul (x : ZMod 19) : z19 x * z19 (-x) = 1 := by
  rw [← z19_add]; simp [z19_zero]

