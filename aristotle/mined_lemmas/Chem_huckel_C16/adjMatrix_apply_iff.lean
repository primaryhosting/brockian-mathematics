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

lemma adjMatrix_apply_iff (i j : Fin 16) :
    (SimpleGraph.cycleGraph 16).Adj i j ↔ (j = i - 1 ∨ j = i + 1) := by
  revert i j; decide

