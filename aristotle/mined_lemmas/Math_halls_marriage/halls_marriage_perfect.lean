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

theorem halls_marriage_perfect [Fintype α] [Fintype β] [DecidableEq β]
    (hcard : Fintype.card α = Fintype.card β) (Adj : α → β → Prop)
    [∀ a, DecidablePred (Adj a)] :
    (∃ f : α → β, Function.Bijective f ∧ ∀ a, Adj a (f a)) ↔
      ∀ s : Finset α, #s ≤ #(s.biUnion (neighbors Adj)) := by
  rw [← halls_marriage Adj]
  constructor
  · rintro ⟨f, hf, hadj⟩
    exact ⟨f, hf.injective, hadj⟩
  · rintro ⟨f, hf, hadj⟩
    exact ⟨f, (Fintype.bijective_iff_injective_and_card f).2 ⟨hf, hcard⟩, hadj⟩

end Math

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

