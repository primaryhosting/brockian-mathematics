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

theorem ff_neg (k : ZMod 9) : ff (-k) = (ff k)⁻¹ := by
  have h : ff k * ff (-k) = 1 := by rw [← ff_add, add_neg_cancel, ff_zero]
  exact (inv_eq_of_mul_eq_one_right h).symm

