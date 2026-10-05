/-
# Halls Marriage
Category: Pure Mathematics
Target: Math.halls_marriage
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Finset

namespace Math

variable {α β : Type*}

/-- The neighbourhood of a left vertex `a` in the bipartite graph with adjacency
relation `Adj : α → β → Prop`: the finset of right vertices adjacent to `a`. -/

theorem mem_neighbors [Fintype β] [DecidableEq β] (Adj : α → β → Prop)
    [∀ a, DecidablePred (Adj a)] {a : α} {b : β} :
    b ∈ neighbors Adj a ↔ Adj a b := by
  simp [neighbors]

/-- **Hall's marriage theorem**. For a bipartite graph with left vertex set `α`, right
vertex set `β` and adjacency relation `Adj`, there is a matching saturating `α`
(an injective choice `f` of a neighbour for each left vertex) if and only if Hall's
condition holds: every finite set `s` of left vertices has at least `#s` neighbours. -/
