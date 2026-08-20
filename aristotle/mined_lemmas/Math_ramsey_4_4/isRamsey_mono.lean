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

lemma isRamsey_mono {m n s t : ℕ} (h : IsRamsey m s t) (hmn : m ≤ n) : IsRamsey n s t := by
  intro G
  set f : Fin m → Fin n := Fin.castLE hmn with hf
  have hinj : Function.Injective f := Fin.castLE_injective hmn
  rcases h (SimpleGraph.comap f G) with ⟨A, -, hc, hr⟩ | ⟨B, -, hc, hb⟩
  · refine Or.inl ⟨A.image f, Finset.subset_univ _, ?_, ?_⟩
    · rw [Finset.card_image_of_injective _ hinj, hc]
    · intro x hx y hy hxy
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hy
      exact hr a ha b hb (fun hc => hxy (by rw [hc]))
  · refine Or.inr ⟨B.image f, Finset.subset_univ _, ?_, ?_⟩
    · rw [Finset.card_image_of_injective _ hinj, hc]
    · intro x hx y hy hxy
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨b, hb', rfl⟩ := Finset.mem_image.1 hy
      exact hb a ha b hb' (fun hc => hxy (by rw [hc]))

