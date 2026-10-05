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

lemma g_mul_nineteen (q : ℕ) : g (19 * q) = 1 := by
  induction q with
  | zero => simp [g_zero]
  | succ n ih =>
      have : 19 * (n + 1) = 19 * n + 19 := by ring
      rw [this, g_add, ih, g_nineteen, one_mul]

