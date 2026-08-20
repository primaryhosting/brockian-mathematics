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

theorem nonNbrs_noClique {k : ℕ} {s : Finset V} {v : V} (hv : v ∈ s)
    (hk : NoCliqueIn Gᶜ (k + 1) s) :
    NoCliqueIn Gᶜ k (s \ insert v (G.neighborFinset v)) := by
  intro t ht hcl
  have hvt : v ∉ t := by
    intro hvt
    have := ht hvt
    simp at this
  refine hk (insert v t) (Finset.insert_subset hv (ht.trans Finset.sdiff_subset)) ⟨?_, ?_⟩
  · rw [Finset.coe_insert]
    refine hcl.1.insert ?_
    intro b hb hvb
    have hb' := ht (by exact_mod_cast hb)
    simp only [Finset.mem_sdiff, Finset.mem_insert, mem_neighborFinset, not_or] at hb'
    exact ⟨hvb, hb'.2.2⟩
  · rw [Finset.card_insert_of_notMem hvt, hcl.2]

