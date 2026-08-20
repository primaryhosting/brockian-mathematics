import Mathlib

/-!
# Correctness of Dijkstra's algorithm

We model a finite weighted digraph on a finite vertex type `V` by a weight function
`w : V → V → ℝ≥0∞`.  Using `ℝ≥0∞` (extended nonnegative reals) as the weight type
encodes exactly the hypotheses of Dijkstra's algorithm:

* every weight is nonnegative;
* `w u v = ⊤` means "there is no edge from `u` to `v`" (an infinitely expensive edge).

A *path* starting at `x` is a list `l : List V` of the vertices visited after `x`.
`pathCost w x l` is its total weight and `pathEnd x l` its final vertex.
`spDist w s t` is the shortest-path distance, the infimum of the costs of all paths
from `s` to `t` (`⊤` if `t` is unreachable from `s`).

`dijkstra w s` runs the usual Dijkstra loop (`Fintype.card V` rounds of
"extract an unvisited vertex of minimal tentative distance, then relax its outgoing
edges"), and the main theorem `CS.dijkstra_correct` states that it returns exactly
the shortest-path distances from `s`.

The two mathematical ingredients are isolated as `CS.key_extract` (the extracted
vertex already has its final distance — this is the step that uses nonnegativity of
the weights) and `CS.key_update` (relaxing the edges out of the extracted vertex
updates the restricted distances correctly).
-/

open scoped Classical ENNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CS

variable {V : Type*}

/-! ## Paths -/

/-- The endpoint of the path that starts at `x` and then visits the vertices of `l`. -/

lemma exampleWeight_spDist : spDist exampleWeight 0 1 = 5 := by
  refine le_antisymm ?_ (le_spDist ?_)
  · calc spDist exampleWeight 0 1 ≤ pathCost exampleWeight 0 [1] := spDist_le _ rfl
      _ = 5 := by simp [pathCost, exampleWeight]
  · intro l hl
    match l with
    | [] => exact absurd hl (by decide)
    | y :: l' =>
      fin_cases y
      · simp [pathCost, exampleWeight]
      · rw [pathCost]
        refine le_trans ?_ le_self_add
        simp [exampleWeight]

/-- Dijkstra's algorithm returns `5`, as it should. -/
example : dijkstra exampleWeight 0 1 = 5 := by
  rw [dijkstra_correct, exampleWeight_spDist]

example : spDist exampleWeight 1 0 = ⊤ := by
  refine le_antisymm le_top (le_spDist ?_)
  intro l hl
  match l with
  | [] => exact absurd hl (by decide)
  | y :: l' =>
    have : exampleWeight 1 y = ⊤ := by
      fin_cases y <;> simp [exampleWeight]
    rw [pathCost, this, top_add]

end Sanity

end CS

import Mathlib
import RequestProject.Dijkstra

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

