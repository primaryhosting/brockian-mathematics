import Mathlib

/-!
# Huckel C 13
Category: Chemistry
Target: Chem.huckel_C13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
open scoped Real

namespace Chem

/-! ### A primitive 13-th root of unity -/

/-- A primitive 13-th root of unity. -/

lemma neighborFinset_cycle13 (j : Fin 13) :
    (SimpleGraph.cycleGraph 13).neighborFinset j = {j - 1, j + 1} :=
  SimpleGraph.cycleGraph_neighborFinset (n := 11) (v := j)

/-- The key computation: `A · P = P · D`, i.e. the columns of `P` are eigenvectors of `A`. -/
