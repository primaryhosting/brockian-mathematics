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

lemma matchingSubgraph_isPerfectMatching (r : V → W → Prop) (e : V ≃ W) (he : ∀ v, r v (e v)) :
    (matchingSubgraph r e he).IsPerfectMatching := by
  constructor
  · rintro (v | w) -
    · refine ⟨Sum.inr (e v), Or.inl ⟨v, rfl, rfl⟩, ?_⟩
      rintro (v' | w') (⟨u, h1, h2⟩ | ⟨u, h1, h2⟩) <;> simp_all
    · refine ⟨Sum.inl (e.symm w), Or.inr ⟨e.symm w, rfl, by simp⟩, ?_⟩
      rintro (v' | w') (⟨u, h1, h2⟩ | ⟨u, h1, h2⟩) <;> simp_all
  · intro v; trivial

/-- From a perfect matching of the bipartite graph of `r` one extracts an equivalence
between the two sides which is compatible with `r`. -/
