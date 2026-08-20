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

/-
Covers, costs, and minimum fragments (Park–Pham).
-/
import Mathlib
import RequestProject.KahnKalai.Measure

open Finset
open scoped Classical

namespace Math2

variable {α : Type*} [DecidableEq α]

/-! ## Covers and their costs -/

/-- `G` is a cover of `H`: every member of `H` contains a member of `G`. -/

lemma covCost_empty {q : ℝ} (hq : 0 ≤ q) : covCost q (∅ : Finset (Finset α)) = 0 := by
  refine le_antisymm ?_ (covCost_nonneg hq _)
  have : covCost q (∅ : Finset (Finset α)) ≤ cost q ∅ :=
    covCost_le_cost hq (by intro S hS; simp at hS)
  simpa [cost] using this

/-! ## Minimum fragments -/

/-- The candidate fragments of `S` with respect to `W`: sets of the form `S' \ W` for
edges `S'` of `H` inside `W ∪ S`. -/
