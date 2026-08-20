/-
# Cantor No Injection From Powerset
Category: Frontier — Set Theory
Target: Infinity.cantor_no_injection_from_powerset
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Cantor No Injection From Powerset
Category: Frontier — Set Theory
Target: Infinity.cantor_no_injection_from_powerset
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Infinity

/-- Key intermediate lemma (diagonal argument): no map `g : Set X → X` is injective.

Given `g`, consider the diagonal set `A = {a | ∀ S, g S = a → a ∉ S}` and the point
`g A`. Membership of `g A` in `A` is contradictory in both directions, the second
direction using injectivity of `g`. This is also available in Mathlib as
`Function.cantor_injective`. -/

theorem no_injective_from_powerset {X : Type*} (g : Set X → X) :
    ¬ Function.Injective g := by
  intro hg
  let A : Set X := {a : X | ∀ S : Set X, g S = a → a ∉ S}
  by_cases h : g A ∈ A
  · exact h A rfl h
  · have h' : ∃ S : Set X, g S = g A ∧ g A ∈ S := by
      simpa [A, Set.mem_setOf_eq, not_forall] using h
    obtain ⟨S, hS, hmem⟩ := h'
    exact h (hg hS ▸ hmem)

/-- Dual Cantor theorem: for any type `X`, no function `g : Set X → X` is injective. -/
