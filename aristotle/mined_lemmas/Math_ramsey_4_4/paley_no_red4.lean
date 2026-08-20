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

lemma paley_no_red4 {A : Finset (Fin 17)} (hA : A.card = 4) : ¬ RedClique paley A := by
  intro hr
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, rfl⟩ := Finset.card_eq_four.1 hA
  have h := (paley_key a b c d hab hac had hbc hbd hcd).1
  have ma : a ∈ ({a, b, c, d} : Finset (Fin 17)) := by simp
  have mb : b ∈ ({a, b, c, d} : Finset (Fin 17)) := by simp
  have mc : c ∈ ({a, b, c, d} : Finset (Fin 17)) := by simp
  have md : d ∈ ({a, b, c, d} : Finset (Fin 17)) := by simp
  have h1 := hr a ma b mb hab
  have h2 := hr a ma c mc hac
  have h3 := hr a ma d md had
  have h4 := hr b mb c mc hbc
  have h5 := hr b mb d md hbd
  have h6 := hr c mc d md hcd
  rw [paley_adj_iff] at h1 h2 h3 h4 h5 h6
  rw [h1, h2, h3, h4, h5, h6] at h
  simp at h

