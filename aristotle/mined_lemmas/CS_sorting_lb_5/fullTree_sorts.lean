/-
# Sorting Lb 5
Category: Computer Science
Target: CS.sorting_lb_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace CS

/-- A comparison-based decision tree for sorting `5` elements.
A `node (a, b) l r` compares the input entries at positions `a` and `b`, continuing in `l`
if the comparison oracle answers `true` and in `r` otherwise; a `leaf p` outputs the
permutation `p`. -/
inductive DTree : Type
  | leaf : Equiv.Perm (Fin 5) → DTree
  | node : Fin 5 × Fin 5 → DTree → DTree → DTree
  deriving Inhabited

namespace DTree

/-- Worst-case number of comparisons performed by the tree. -/

theorem fullTree_sorts : Sorts fullTree := by
  intro p
  refine run_build allPairs _ p (by simp) ?_
  intro q _ hq
  exact oracle_injective fun a b => hq (a, b) (mem_allPairs a b)

end DTree

/-- The hypothesis of `sorting_lb_5` is satisfiable: comparison sorts of `5` elements exist. -/
