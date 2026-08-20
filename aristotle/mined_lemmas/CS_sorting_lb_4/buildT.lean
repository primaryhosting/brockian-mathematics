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

noncomputable def buildT : List (Fin 4 × Fin 4) → Finset (Equiv.Perm (Fin 4)) → DTree
  | [], ps => .leaf (if h : ps.Nonempty then h.choose else 1)
  | (i, j) :: rest, ps =>
      .node i j (buildT rest (ps.filter fun τ => τ i < τ j))
        (buildT rest (ps.filter fun τ => ¬ τ i < τ j))

