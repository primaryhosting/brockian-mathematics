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

lemma zeta_add (a b : ZMod 16) : zeta (a + b) = zeta a * zeta b := by
  simp only [zeta, ZMod.val_add, w_pow_mod, pow_add]

