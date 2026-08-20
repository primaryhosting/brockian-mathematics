/-
# Sorting Lb 4
Category: Computer Science
Target: CS.sorting_lb_4
Verification: verified (axiom-clean: propext, Classical.choice, Quot.sound)
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace CS

/-- A comparison-based decision tree sorting 4 elements.  A `leaf` outputs a
permutation (the claimed sorted order / ranking of the input), and a `node i j`
compares the input keys at positions `i` and `j` and branches accordingly. -/
inductive DTree where
  | leaf : Equiv.Perm (Fin 4) → DTree
  | node : Fin 4 → Fin 4 → DTree → DTree → DTree
  deriving Inhabited

namespace DTree

/-- The worst-case number of comparisons performed by the tree. -/

theorem mem_allPairs : ∀ p : Fin 4 × Fin 4, p ∈ allPairs := by decide

/-- The brute-force decision tree: perform every comparison in `L`, restricting
the set `ps` of candidate answers accordingly, and output a surviving candidate. -/
