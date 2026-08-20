import Mathlib

/-!
# Hall's marriage theorem

A bipartite graph has a matching saturating one side iff Hall's condition holds,
and (when the two sides have the same size) a perfect matching iff Hall's condition holds.
-/

namespace Math

open Finset

variable {L R : Type*} [Fintype L] [Fintype R] [DecidableEq R]
  (r : L → R → Prop) [∀ a, DecidablePred (r a)]

/-- The set of neighbours of a left vertex `a` in the bipartite graph given by `r`. -/

def HallCondition : Prop :=
  ∀ s : Finset L, s.card ≤ (s.biUnion (neighbors r)).card

/-- There is a matching saturating the left side: an injective choice of a neighbour
for every left vertex. -/
