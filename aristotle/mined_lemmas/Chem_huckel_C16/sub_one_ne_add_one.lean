/-
# Huckel C 16
Category: Chemistry
Target: Chem.huckel_C16
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Matrix Complex

/-- A primitive 16-th root of unity. -/

lemma sub_one_ne_add_one (i : Fin 16) : i - 1 ≠ i + 1 := by
  revert i; decide

