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

theorem card_split (G : SimpleGraph V) [DecidableRel G.Adj] (s : Finset V) (v : V) :
    s.card ≤ 1 + (s ∩ G.neighborFinset v).card + (s \ insert v (G.neighborFinset v)).card := by
  have hsub : s ⊆ insert v ((s ∩ G.neighborFinset v) ∪ (s \ insert v (G.neighborFinset v))) := by
    intro x hx
    by_cases hxv : x = v
    · simp [hxv]
    · by_cases hadj : G.Adj v x
      · simp [Finset.mem_insert, Finset.mem_union, Finset.mem_inter, hx, hadj]
      · simp [Finset.mem_insert, Finset.mem_union, Finset.mem_sdiff, hx, hxv, hadj]
  calc s.card ≤ _ := Finset.card_le_card hsub
    _ ≤ 1 + ((s ∩ G.neighborFinset v) ∪ (s \ insert v (G.neighborFinset v))).card := by
        simp [Nat.add_comm]
    _ ≤ 1 + ((s ∩ G.neighborFinset v).card + (s \ insert v (G.neighborFinset v)).card) := by
        exact Nat.add_le_add_left (Finset.card_union_le _ _) 1
    _ = 1 + (s ∩ G.neighborFinset v).card + (s \ insert v (G.neighborFinset v)).card := by ring

omit [Fintype V] in
/-- `R(2,3)`-type bound: a triangle-free graph whose vertex set `s` induces a complete graph
has at most `2` vertices. -/
