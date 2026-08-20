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

lemma card_redN_add_card_blueN (hv : v ∈ S) :
    (redN G S v).card + (blueN G S v).card + 1 = S.card := by
  have hsplit : (S.filter (fun y => G.Adj v y)).card
      + (S.filter (fun y => ¬ G.Adj v y)).card = S.card :=
    Finset.card_filter_add_card_filter_not _
  have hins : S.filter (fun y => ¬ G.Adj v y) = insert v (blueN G S v) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_insert, mem_blueN]
    constructor
    · rintro ⟨hyS, hadj⟩
      by_cases h : y = v
      · exact Or.inl h
      · exact Or.inr ⟨hyS, h, hadj⟩
    · rintro (rfl | ⟨hyS, _, hadj⟩)
      · exact ⟨hv, by simp⟩
      · exact ⟨hyS, hadj⟩
  have hvnot : v ∉ blueN G S v := by simp [mem_blueN]
  rw [hins, Finset.card_insert_of_notMem hvnot] at hsplit
  simpa [redN] using hsplit

