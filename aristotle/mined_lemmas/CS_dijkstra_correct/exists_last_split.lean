import Mathlib

/-!
# Dijkstra Correct
Category: Computer Science
Target: CS.dijkstra_correct
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

namespace CS

/-! ## Walks

A walk starting at a vertex `src` is described by the list `l` of vertices it visits
after `src`, in order.  Since we work with a complete weighted graph (a non-edge can be
modelled by a suitably large weight), every list of vertices describes a walk. -/

section Walks

variable {V : Type*}

/-- The final vertex of the walk that starts at `src` and then visits `l` in order. -/

lemma exists_last_split [DecidableEq V] (u : V) (l : List V) (h : u ∈ l) :
    ∃ l₁ l₂ : List V, l = l₁ ++ u :: l₂ ∧ u ∉ l₂ := by
  induction l with
  | nil => simp at h
  | cons a t ih =>
      by_cases ht : u ∈ t
      · obtain ⟨l₁, l₂, h1, h2⟩ := ih ht
        exact ⟨a :: l₁, l₂, by simp [h1], h2⟩
      · have : a = u := by
          rcases List.mem_cons.1 h with h' | h'
          · exact h'.symm
          · exact absurd h' ht
        exact ⟨[], t, by simp [this], ht⟩

/-- Splitting a list at the first element outside a finite set. -/
