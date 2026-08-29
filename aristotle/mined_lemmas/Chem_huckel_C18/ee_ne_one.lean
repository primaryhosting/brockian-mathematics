import Mathlib

/-!
# Huckel C 18
Category: Chemistry
Target: Chem.huckel_C18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Real Matrix Finset

/-- A primitive 18-th root of unity. -/

lemma ee_ne_one (c : ZMod 18) (hc : c ≠ 0) : ee c ≠ 1 := by
  have h1 : c.val ≠ 0 := fun h => hc ((ZMod.val_eq_zero c).mp h)
  exact om_prim.pow_ne_one_of_pos_of_lt h1 (ZMod.val_lt c)

/-- Orthogonality relation for the character `ee`. -/
