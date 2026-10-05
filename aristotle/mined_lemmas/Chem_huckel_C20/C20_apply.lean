import Mathlib

/-!
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Finset Matrix

/-- A primitive 20-th root of unity. -/

lemma C20_apply (i j : ZMod 20) : C20 i j = if i - j = 1 ∨ j - i = 1 then 1 else 0 := by
  simp [C20, SimpleGraph.adjMatrix_apply, SimpleGraph.cycleGraph_adj]

/-- The candidate eigenvector for the eigenvalue `2 cos (2πk/20)`. -/
