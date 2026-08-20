import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Math

open Finset Function

variable {V W : Type*}

/-- The bipartite graph on `V ⊕ W` determined by a relation `r : V → W → Prop`:
the only edges join a vertex `v` of the left part to a vertex `w` of the right part,
and such an edge is present exactly when `r v w` holds. -/

def matchingSubgraph (r : V → W → Prop) (e : V ≃ W) (he : ∀ v, r v (e v)) :
    (bipartiteGraph r).Subgraph where
  verts := Set.univ
  Adj a b := (∃ v, a = Sum.inl v ∧ b = Sum.inr (e v)) ∨ (∃ v, b = Sum.inl v ∧ a = Sum.inr (e v))
  adj_sub := by
    rintro a b (⟨v, rfl, rfl⟩ | ⟨v, rfl, rfl⟩)
    · simpa using he v
    · simpa using he v
  edge_vert := by intro a b _; trivial
  symm := by
    rintro a b (h | h)
    · exact Or.inr h
    · exact Or.inl h

