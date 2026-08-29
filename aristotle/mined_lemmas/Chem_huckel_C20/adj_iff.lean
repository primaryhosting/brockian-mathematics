import Mathlib

/-!
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real

set_option maxHeartbeats 1000000

namespace Chem

open Complex Matrix Polynomial Finset

/-- A primitive 20-th root of unity. -/

lemma adj_iff (i j : Fin 20) :
    (SimpleGraph.cycleGraph 20).Adj i j ↔ (j = i - 1 ∨ j = i + 1) := by
  revert i j
  decide +kernel

