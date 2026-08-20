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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

import Mathlib

/-!
# Arrow's impossibility theorem

A *ranking* on a type of alternatives `A` is a total, transitive, antisymmetric relation
(a linear order presented as a relation).  A *profile* assigns a ranking to each voter, and a
*ranked voting rule* (social welfare function) aggregates profiles into a single relation.

The main result, `Frontier.arrow_impossibility`, states that whenever there are at least three
alternatives and finitely many voters, no ranked voting rule producing a ranking can
simultaneously satisfy unanimity (Pareto), independence of irrelevant alternatives, and
non-dictatorship.
-/

namespace Frontier

section Defs

variable {A : Type*}

/-- A *ranking* of the alternatives: a total, transitive, antisymmetric relation. -/

lemma isRanking_putBot (h : IsRanking r) (b : A) : IsRanking (putBot b r) := by
  refine ⟨?_, ?_, ?_⟩
  · intro s t
    by_cases ht : t = b
    · exact Or.inl (Or.inl ht)
    · by_cases hs : s = b
      · exact Or.inr (Or.inl hs)
      · rcases h.total s t with hst | hts
        · exact Or.inl (Or.inr ⟨hs, hst⟩)
        · exact Or.inr (Or.inr ⟨ht, hts⟩)
  · rintro s t u hst (rfl | ⟨ht, htu⟩)
    · exact Or.inl rfl
    · rcases hst with (rfl | ⟨hs, hst⟩)
      · exact absurd rfl ht
      · exact Or.inr ⟨hs, h.trans hst htu⟩
  · rintro s t (rfl | ⟨hs, hst⟩) hts
    · rcases hts with (rfl | ⟨h1, _⟩)
      · rfl
      · exact absurd rfl h1
    · rcases hts with (rfl | ⟨_, hts⟩)
      · exact absurd rfl hs
      · exact h.antisymm hst hts

