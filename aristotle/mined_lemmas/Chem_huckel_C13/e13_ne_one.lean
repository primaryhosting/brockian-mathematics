import Mathlib
/-!
# Huckel C 13
Category: Chemistry
Target: Chem.huckel_C13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real
open Complex Matrix

namespace Chem

/-- A primitive 13-th root of unity. -/

lemma e13_ne_one {m : ZMod 13} (hm : m ≠ 0) : e13 m ≠ 1 := by
  have hlt : m.val < 13 := ZMod.val_lt m
  have hpos : m.val ≠ 0 := fun h0 => hm ((ZMod.val_eq_zero m).mp h0)
  exact isPrimitiveRoot_omega13.pow_ne_one_of_pos_of_lt hpos hlt

/-- Character orthogonality on `ZMod 13`. -/
