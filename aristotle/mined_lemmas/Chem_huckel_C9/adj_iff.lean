import Mathlib

/-!
# Huckel C 9
Category: Chemistry
Target: Chem.huckel_C9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators Real
open Complex Polynomial

namespace Chem

/-- A primitive 9th root of unity. -/

theorem adj_iff (j l : Fin 9) :
    (SimpleGraph.cycleGraph 9).Adj j l ↔ (l = j + 1 ∨ l = j - 1) := by revert j l; decide

