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

lemma exists_first_split [DecidableEq V] (S : Finset V) (l : List V) (h : ∃ x ∈ l, x ∉ S) :
    ∃ (l₁ : List V) (b : V) (l₂ : List V),
      l = l₁ ++ b :: l₂ ∧ (∀ y ∈ l₁, y ∈ S) ∧ b ∉ S := by
  induction l with
  | nil => simp at h
  | cons a t ih =>
      by_cases ha : a ∈ S
      · have ht : ∃ x ∈ t, x ∉ S := by
          obtain ⟨x, hx, hxS⟩ := h
          rcases List.mem_cons.1 hx with rfl | hx'
          · exact absurd ha hxS
          · exact ⟨x, hx', hxS⟩
        obtain ⟨l₁, b, l₂, h1, h2, h3⟩ := ih ht
        refine ⟨a :: l₁, b, l₂, by simp [h1], ?_, h3⟩
        intro y hy
        rcases List.mem_cons.1 hy with rfl | hy'
        · exact ha
        · exact h2 y hy'
      · exact ⟨[], a, t, by simp, by simp, ha⟩

end Walks

/-! ## The algorithm -/

section Algorithm

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A vertex of `s` minimising `d`. -/
