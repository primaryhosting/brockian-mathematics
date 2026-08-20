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

lemma exists_ne_two (h3 : ∃ a b c : A, a ≠ b ∧ a ≠ c ∧ b ≠ c) (x y : A) :
    ∃ t : A, t ≠ x ∧ t ≠ y := by
  obtain ⟨a, b, c, hab, hac, hbc⟩ := h3
  by_cases h1 : a ≠ x ∧ a ≠ y
  · exact ⟨a, h1⟩
  by_cases h2 : b ≠ x ∧ b ≠ y
  · exact ⟨b, h2⟩
  by_cases h3 : c ≠ x ∧ c ≠ y
  · exact ⟨c, h3⟩
  push_neg at h1 h2 h3
  have ha : a = x ∨ a = y := by by_cases h : a = x; exacts [Or.inl h, Or.inr (h1 h)]
  have hb : b = x ∨ b = y := by by_cases h : b = x; exacts [Or.inl h, Or.inr (h2 h)]
  have hc : c = x ∨ c = y := by by_cases h : c = x; exacts [Or.inl h, Or.inr (h3 h)]
  rcases ha with rfl | rfl <;> rcases hb with h | h <;> rcases hc with h' | h' <;> simp_all

/-- **Arrow's theorem** (existence-of-a-dictator form). -/
