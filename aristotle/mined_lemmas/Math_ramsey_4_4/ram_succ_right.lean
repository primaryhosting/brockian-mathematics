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

lemma ram_succ_right (hv : v ∈ S) (h : Ram G (blueN G S v) s t) : Ram G S s (t + 1) := by
  rcases h with ⟨A, hA, hc, hr⟩ | ⟨B, hB, hc, hb⟩
  · exact Or.inl ⟨A, hA.trans blueN_subset, hc, hr⟩
  · have hvB : v ∉ B := by
      intro hmem
      exact ((mem_blueN (G := G) (S := S) (v := v)).1 (hB hmem)).2.1 rfl
    refine Or.inr ⟨insert v B, ?_, ?_, ?_⟩
    · intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact hv
      · exact blueN_subset (hB hx)
    · rw [Finset.card_insert_of_notMem hvB, hc]
    · exact blueClique_insert hvB (fun y hy => ((mem_blueN (G := G)).1 (hB hy)).2.2) hb

