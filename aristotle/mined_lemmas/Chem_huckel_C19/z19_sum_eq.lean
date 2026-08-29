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

lemma z19_sum_eq (c : ZMod 19) :
    ∑ k : ZMod 19, z19 (c * k) = if c = 0 then 19 else 0 := by
  by_cases hc : c = 0
  · simp [hc, z19_zero]
  · simp [hc, z19_sum_ne_zero hc]

