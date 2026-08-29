import Mathlib

/-!
# Huckel C 12
Category: Chemistry
Target: Chem.huckel_C12
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real

set_option maxHeartbeats 1000000

namespace Chem

open Complex Polynomial Matrix Finset

/-- The primitive 12-th root of unity `exp(2πi/12)`. -/

lemma zeta12_ne_one {m : ZMod 12} (hm : m ≠ 0) : zeta12 m ≠ 1 :=
  isPrimitiveRoot_w12.pow_ne_one_of_pos_of_lt ((ZMod.val_ne_zero m).mpr hm) (ZMod.val_lt m)

