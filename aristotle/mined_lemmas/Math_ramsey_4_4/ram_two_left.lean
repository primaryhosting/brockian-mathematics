import RequestProject.Ramsey
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
# The Ramsey number `R(4,4) = 18`

We define two-colourings of the edges of a complete graph as simple graphs (`red` = adjacent,
`blue` = non-adjacent), and prove that every graph on 18 vertices contains a red or a blue
clique on 4 vertices, while the Paley graph on 17 vertices contains neither.
-/

open Finset
open scoped Classical

namespace Math

variable {V : Type*} {G : SimpleGraph V} {S S' : Finset V} {s t : ℕ} {v : V}

/-- `A` is a set of vertices, all pairs of which are adjacent (a "red" clique). -/

lemma ram_two_left (h : t ≤ S.card) : Ram G S 2 t := by
  by_cases hedge : ∃ x ∈ S, ∃ y ∈ S, x ≠ y ∧ G.Adj x y
  · obtain ⟨x, hx, y, hy, hxy, hadj⟩ := hedge
    refine Or.inl ⟨{x, y}, ?_, ?_, ?_⟩
    · intro z hz
      rcases Finset.mem_insert.1 hz with rfl | hz
      · exact hx
      · rw [Finset.mem_singleton] at hz; subst hz; exact hy
    · rw [Finset.card_insert_of_notMem (by simpa using hxy), Finset.card_singleton]
    · intro a ha b hb hab
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact absurd rfl hab
      · exact hadj
      · exact hadj.symm
      · exact absurd rfl hab
  · push_neg at hedge
    obtain ⟨B, hBS, hB⟩ := Finset.exists_subset_card_eq h
    exact Or.inr ⟨B, hBS, hB, fun x hx y hy hxy => hedge x (hBS hx) y (hBS hy) hxy⟩

