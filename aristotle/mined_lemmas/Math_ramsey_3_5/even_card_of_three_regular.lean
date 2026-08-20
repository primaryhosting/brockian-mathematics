import Mathlib
import RequestProject.Ramsey

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
# The Ramsey number `R(3,5) = 14`

This file proves that `14` is the least `n` such that every simple graph on `n` vertices
contains a triangle (a `3`-clique) or an independent set of size `5` (a `5`-clique of the
complement).
-/

namespace Math

open Finset SimpleGraph

section Bounds

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- `NoCliqueIn G n s` says that `G` has no `n`-clique contained in the vertex set `s`. -/

theorem even_card_of_three_regular {s : Finset V}
    (h : ∀ v ∈ s, (s ∩ G.neighborFinset v).card = 3) : Even s.card := by
  classical
  set G' : SimpleGraph V :=
    { Adj := fun a b => G.Adj a b ∧ a ∈ s ∧ b ∈ s
      symm := fun a b hab => ⟨hab.1.symm, hab.2.2, hab.2.1⟩
      loopless := ⟨fun a ha => G.irrefl ha.1⟩ } with hG'
  haveI : DecidableRel G'.Adj := fun a b => by
    rw [hG']
    exact inferInstanceAs (Decidable (G.Adj a b ∧ a ∈ s ∧ b ∈ s))
  have hdeg : ∀ v : V, G'.neighborFinset v = if v ∈ s then s ∩ G.neighborFinset v else ∅ := by
    intro v
    ext u
    by_cases hv : v ∈ s <;>
      simp [hv, mem_neighborFinset, hG', Finset.mem_inter, and_comm]
  have key : Finset.univ.filter (fun v => Odd (G'.degree v)) = s := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hodd
      by_contra hv
      rw [SimpleGraph.degree, hdeg v, if_neg hv] at hodd
      simp at hodd
    · intro hv
      rw [SimpleGraph.degree, hdeg v, if_pos hv, h v hv]
      decide
  have h2 := G'.even_card_odd_degree_vertices
  rwa [key] at h2

/-- `R(3,4) ≤ 9`. -/
