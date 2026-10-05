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
# Friendship Theorem
Category: Frontier — Fields Medal Work
Target: Frontier.friendship_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open Finset Matrix SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A graph satisfies the *friendship condition* when any two distinct vertices have
exactly one common neighbour ("every two people have exactly one common friend"). -/

lemma card_common_neighbors_eq_one (hG : Friendship G) {v w : V} (h : v ≠ w) :
    (G.neighborFinset v ∩ G.neighborFinset w).card = 1 := by
  obtain ⟨u, hu, huniq⟩ := hG h
  rw [Finset.card_eq_one]
  refine ⟨u, ?_⟩
  ext x
  simp only [Finset.mem_inter, mem_neighborFinset, Finset.mem_singleton]
  constructor
  · rintro ⟨h1, h2⟩
    exact huniq x ⟨h1, h2⟩
  · rintro rfl
    exact hu

/-- The square of the adjacency matrix counts common neighbours. -/
