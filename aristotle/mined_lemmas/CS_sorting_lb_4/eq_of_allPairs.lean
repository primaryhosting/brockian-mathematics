import Mathlib

/-!
# Sorting Lb 4
Category: Computer Science
Target: CS.sorting_lb_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

/-- A comparison-based decision tree for sorting four elements.
Each internal node compares two positions `i j` of the input; the algorithm
branches on the answer.  Each leaf outputs a permutation (the claimed sorted
order of the input). -/
inductive CompTree : Type
  | leaf (out : Equiv.Perm (Fin 4)) : CompTree
  | node (i j : Fin 4) (l r : CompTree) : CompTree
  deriving Inhabited

namespace CompTree

/-- The worst-case number of comparisons performed by the tree. -/

theorem eq_of_allPairs (p q : Equiv.Perm (Fin 4))
    (h : ∀ ij ∈ allPairs, (q ij.1 < q ij.2 ↔ p ij.1 < p ij.2)) : q = p := by
  revert h
  revert p q
  decide

/-- The hypothesis of the lower bound is satisfiable: some decision tree really
does sort four elements (the naive one, using all six comparisons). -/
