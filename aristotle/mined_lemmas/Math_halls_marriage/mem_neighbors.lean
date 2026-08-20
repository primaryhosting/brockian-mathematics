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

@[simp] lemma mem_neighbors {a : L} {b : R} : b ∈ neighbors r a ↔ r a b := by
  simp [neighbors]

/-- Hall's condition: every set of left vertices has at least as many neighbours. -/
