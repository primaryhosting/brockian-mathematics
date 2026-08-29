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

lemma zeta_ne_zero (a : ZMod 16) : zeta a ≠ 0 := by
  have : w ≠ 0 := by
    simp [w, Complex.exp_ne_zero]
  exact pow_ne_zero _ this

