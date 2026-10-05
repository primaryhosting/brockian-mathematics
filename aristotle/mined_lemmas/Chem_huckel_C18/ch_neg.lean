/-
# Huckel C 18
Category: Chemistry
Target: Chem.huckel_C18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 18
Category: Chemistry
Target: Chem.huckel_C18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open Complex

namespace Chem

/-- A primitive 18-th root of unity. -/

theorem ch_neg (x : Fin 18) : ch (-x) = (ch x)⁻¹ := by
  have h : ch x * ch (-x) = 1 := by rw [← ch_add]; simp [ch_zero]
  exact (DivisionMonoid.inv_eq_of_mul _ _ h).symm

