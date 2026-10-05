/-
# Huckel C 16
Category: Chemistry
Target: Chem.huckel_C16
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators Real

namespace Chem

open Complex Finset

/-- A primitive 16-th root of unity. -/

lemma zeta_neg (a : ZMod 16) : zeta (-a) = (zeta a)⁻¹ := by
  have h : zeta a * zeta (-a) = 1 := by
    rw [← zeta_add]; simp [zeta_zero]
  exact eq_inv_of_mul_eq_one_right h

