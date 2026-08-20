import Mathlib

/-!
# Sorting Lb 5
Category: Computer Science
Target: CS.sorting_lb_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

/-- An input to a comparison sort of 5 elements is a "ranking": a permutation `s` of `Fin 5`
assigning to each position `i` its rank `s i`.  A comparison of positions `i` and `j` returns
`decide (s i < s j)`. -/
abbrev Rank := Equiv.Perm (Fin 5)

/-- A comparison-based decision tree for sorting 5 elements: an internal node compares two
positions and branches on the outcome, a leaf outputs a permutation (the claimed ranking). -/
inductive DTree : Type
  | leaf : Rank → DTree
  | node : Fin 5 → Fin 5 → DTree → DTree → DTree

/-- The worst-case number of comparisons performed by the tree. -/

def ans (L : List (Fin 5 × Fin 5)) (s : Rank) : List Bool :=
  L.map (fun p => decide (s p.1 < s p.2))

/-- The complete decision tree asking exactly the comparisons in `L`, with leaves labelled
by `f` applied to the sequence of answers. -/
