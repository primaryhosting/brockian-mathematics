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

def Sorts (t : CompTree) : Prop := ∀ p : Equiv.Perm (Fin 4), t.run p = p

/-- The six comparisons between distinct positions of a four-element input. -/
