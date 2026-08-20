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
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Chem

open Polynomial Matrix

/-! ## The adjacency matrix of the cycle graph `C₉` -/

/-- The adjacency matrix of the cycle graph `C₉`, i.e. the Hückel matrix of the
cyclononatetraenyl π-system with `α = 0` and `β = 1`. -/

lemma cyc9_adj_iff (i j : Fin 9) :
    (SimpleGraph.cycleGraph 9).Adj i j ↔ (j = i + 1 ∨ j = i - 1) := by
  rw [SimpleGraph.cycleGraph_adj']
  have h1 : ((1 : Fin 9) : ℕ) = 1 := rfl
  rw [← h1, ← Fin.ext_iff, ← Fin.ext_iff]
  constructor
  · rintro (h | h)
    · right; rw [← h, sub_sub_cancel]
    · left; rw [← h, add_sub_cancel]
  · rintro (h | h)
    · right; rw [h, add_sub_cancel_left]
    · left; rw [h, sub_sub_cancel]

