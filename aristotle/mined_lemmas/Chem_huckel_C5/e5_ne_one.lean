/-
# Huckel C 5
Category: Chemistry
Target: Chem.huckel_C5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Huckel C 5
Category: Chemistry
Target: Chem.huckel_C5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset Matrix

namespace Chem

/-- A primitive fifth root of unity. -/

lemma e5_ne_one {m : ZMod 5} (hm : m ≠ 0) : e5 m ≠ 1 :=
  zeta5_primitive.pow_ne_one_of_pos_of_lt ((ZMod.val_ne_zero m).mpr hm) (ZMod.val_lt m)

/-- `e5 k + e5 (-k) = 2 cos (2πk/5)`. -/
