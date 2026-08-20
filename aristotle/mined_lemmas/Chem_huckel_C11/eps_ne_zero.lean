/-
# Huckel C 11
Category: Chemistry
Target: Chem.huckel_C11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Complex Finset

/-- A primitive 11-th root of unity. -/

lemma eps_ne_zero (x : ZMod 11) : eps x ≠ 0 := by
  have : zeta ≠ 0 := zeta_primitive.ne_zero (by norm_num)
  exact pow_ne_zero _ this

