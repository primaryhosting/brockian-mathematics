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

lemma isRanking_liftAbove (h : IsRanking r) : IsRanking (liftAbove z w r) := by
  refine ⟨?_, ?_, ?_⟩
  · intro s t
    by_cases hs : s = z <;> by_cases ht : t = z
    · subst hs; subst ht; exact Or.inl liftAbove_self
    · subst hs
      by_cases htw : t = w
      · subst htw; exact Or.inl ((liftAbove_left ht).2 (h.refl t))
      · rcases h.total w t with h1 | h1
        · exact Or.inl ((liftAbove_left ht).2 h1)
        · exact Or.inr ((liftAbove_right ht).2 ⟨h1, htw⟩)
    · subst ht
      by_cases hsw : s = w
      · subst hsw; exact Or.inr ((liftAbove_left hs).2 (h.refl s))
      · rcases h.total s w with h1 | h1
        · exact Or.inl ((liftAbove_right hs).2 ⟨h1, hsw⟩)
        · exact Or.inr ((liftAbove_left hs).2 h1)
    · rcases h.total s t with h1 | h1
      · exact Or.inl ((liftAbove_of_ne hs ht).2 h1)
      · exact Or.inr ((liftAbove_of_ne ht hs).2 h1)
  · intro s t u hst htu
    by_cases hs : s = z <;> by_cases ht : t = z <;> by_cases hu : u = z
    · subst hs; subst hu; exact liftAbove_self
    · subst hs; subst ht; exact htu
    · subst hs; subst hu; exact liftAbove_self
    · subst hs
      rw [liftAbove_left ht] at hst
      rw [liftAbove_of_ne ht hu] at htu
      exact (liftAbove_left hu).2 (h.trans hst htu)
    · subst ht; subst hu; exact hst
    · subst ht
      rw [liftAbove_right hs] at hst
      rw [liftAbove_left hu] at htu
      exact (liftAbove_of_ne hs hu).2 (h.trans hst.1 htu)
    · subst hu
      rw [liftAbove_of_ne hs ht] at hst
      rw [liftAbove_right ht] at htu
      refine (liftAbove_right hs).2 ⟨h.trans hst htu.1, ?_⟩
      rintro rfl
      exact htu.2 (h.antisymm htu.1 hst)
    · rw [liftAbove_of_ne hs ht] at hst
      rw [liftAbove_of_ne ht hu] at htu
      exact (liftAbove_of_ne hs hu).2 (h.trans hst htu)
  · intro s t hst hts
    by_cases hs : s = z <;> by_cases ht : t = z
    · rw [hs, ht]
    · subst hs
      rw [liftAbove_left ht] at hst
      rw [liftAbove_right ht] at hts
      exact absurd (h.antisymm hts.1 hst) hts.2
    · subst ht
      rw [liftAbove_right hs] at hst
      rw [liftAbove_left hs] at hts
      exact absurd (h.antisymm hst.1 hts) hst.2
    · rw [liftAbove_of_ne hs ht] at hst
      rw [liftAbove_of_ne ht hs] at hts
      exact h.antisymm hst hts

