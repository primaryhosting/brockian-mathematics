import Mathlib

/-!
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset SimpleGraph Matrix

namespace Chem

/-! ### Arithmetic in `Fin 14`

`Fin 14` carries the modular `+`, `-`, `*` and `-·` operations used by
`SimpleGraph.cycleGraph_adj`, but no `CommRing` instance is available for the numeral `14`,
so the handful of ring identities we need are checked by decision procedure. -/

section Fin14


lemma A_apply (j l : Fin 14) :
    A14 j l = (if l = j - 1 then 1 else 0) + (if l = j + 1 then 1 else 0) := by
  have hadj : (cycleGraph 14).Adj j l ↔ (l = j - 1 ∨ l = j + 1) :=
    (SimpleGraph.cycleGraph_adj (n := 12)).trans (fin14_adj_iff j l)
  rw [A14, SimpleGraph.adjMatrix_apply]
  by_cases h1 : l = j - 1
  · subst h1
    rw [if_pos (hadj.mpr (Or.inl rfl)), if_pos rfl, if_neg (fin14_pred_ne_succ j)]
    ring
  · by_cases h2 : l = j + 1
    · subst h2
      rw [if_pos (hadj.mpr (Or.inr rfl)), if_neg h1, if_pos rfl]
      ring
    · rw [if_neg (fun h => (hadj.mp h).elim h1 h2), if_neg h1, if_neg h2]
      ring

