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

lemma redClique_insert {A : Finset V} (hv : v ∉ A) (hadj : ∀ y ∈ A, G.Adj v y)
    (h : RedClique G A) : RedClique G (insert v A) := by
  intro x hx y hy hxy
  simp only [Finset.mem_insert] at hx hy
  rcases hx with rfl | hx
  · rcases hy with rfl | hy
    · exact absurd rfl hxy
    · exact hadj _ hy
  · rcases hy with rfl | hy
    · exact (hadj _ hx).symm
    · exact h _ hx _ hy hxy

