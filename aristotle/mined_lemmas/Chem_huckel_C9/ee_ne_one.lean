import Mathlib

/-!
# Huckel C 9
Category: Chemistry
Target: Chem.huckel_C9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Matrix Finset

noncomputable section

/-- A primitive 9-th root of unity. -/

lemma ee_ne_one {c : ZMod 9} (hc : c ≠ 0) : ee c ≠ 1 :=
  om_primitive.pow_ne_one_of_pos_of_lt ((ZMod.val_ne_zero c).mpr hc) (ZMod.val_lt c)

