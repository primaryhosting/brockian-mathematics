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

def neighbors [Fintype β] [DecidableEq β] (Adj : α → β → Prop)
    [∀ a, DecidablePred (Adj a)] (a : α) : Finset β :=
  univ.filter (fun b => Adj a b)

@[simp]

theorem halls_marriage [Fintype α] [Fintype β] [DecidableEq β] (Adj : α → β → Prop)
    [∀ a, DecidablePred (Adj a)] :
    (∃ f : α → β, Function.Injective f ∧ ∀ a, Adj a (f a)) ↔
      ∀ s : Finset α, #s ≤ #(s.biUnion (neighbors Adj)) := by
  have h := (Finset.all_card_le_biUnion_card_iff_exists_injective (neighbors Adj)).symm
  simpa using h

/-- **Hall's marriage theorem, perfect matching form**. If the two sides of a bipartite
graph have the same (finite) cardinality, then the graph admits a perfect matching -- a
bijection `f : α → β` pairing each left vertex with an adjacent right vertex -- if and only
if Hall's condition holds. -/
