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

def HasLeftMatching : Prop :=
  ∃ f : L → R, Function.Injective f ∧ ∀ a, r a (f a)

omit [Fintype L] in
/-- **Hall's marriage theorem**: the bipartite graph given by `r` has a matching
saturating the left side iff Hall's condition holds. -/
