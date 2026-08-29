/-!
# Huckel C 15
Category: Chemistry
Target: Chem.huckel_C15
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Finset

/-- A primitive 15-th root of unity. -/

lemma ee_ne_one {m : ZMod 15} (hm : m ≠ 0) : ee m ≠ 1 := by
  have h0 : m.val ≠ 0 := by
    simpa [ZMod.val_eq_zero_iff] using hm
  exact zeta_primitive.pow_ne_one_of_pos_of_lt (Nat.pos_of_ne_zero h0) m.val_lt

