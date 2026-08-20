import Mathlib

/-!
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix Finset Complex

set_option maxHeartbeats 1000000

namespace Chem

/-- A primitive 14-th root of unity. -/

lemma cycle_adj_iff (j i : Fin 14) :
    (SimpleGraph.cycleGraph 14).Adj j i ↔ (i = j - 1 ∨ i = j + 1) := by
  revert j i
  decide

