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

namespace Chem

open Complex Matrix

/-- A primitive 12-th root of unity. -/

lemma C12_eq_adjMatrix : C12 = (SimpleGraph.cycleGraph 12).adjMatrix ℂ := by
  ext i j
  have h : ((i.val + 1) % 12 = j.val ∨ (j.val + 1) % 12 = i.val)
      ↔ (SimpleGraph.cycleGraph 12).Adj i j := by
    revert i j; decide
  simp [C12, SimpleGraph.adjMatrix_apply, ← h]

