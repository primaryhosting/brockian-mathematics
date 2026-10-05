/-
# Huckel C 8
Category: Chemistry
Target: Chem.huckel_C8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Classical

set_option maxHeartbeats 4000000

namespace Chem

/-- A primitive 8-th root of unity. -/

lemma mod_eight_iff (k l : Fin 8) : ((k : ℕ) + 7 * (l : ℕ)) % 8 = 0 ↔ k = l := by
  revert k l; decide

