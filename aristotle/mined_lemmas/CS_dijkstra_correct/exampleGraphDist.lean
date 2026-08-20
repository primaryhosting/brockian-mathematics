import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ENNReal

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

/-!
# Dijkstra's algorithm

We formalize Dijkstra's algorithm on a finite directed graph with nonnegative edge weights,
and prove that it computes the shortest-path distances.

Weights take values in `ℝ≥0∞` (the nonnegative extended reals): this encodes both the
nonnegativity of the weights and the absence of an edge (weight `⊤`).

* `CS.walkWeight` : the weight of a walk, given as the list of vertices visited after the source.
* `CS.graphDist w src v` : the shortest-path distance, i.e. the infimum of the weights of
  all walks from `src` to `v`.
* `CS.dijkstra w src` : the output of Dijkstra's algorithm.
* `CS.dijkstra_correct` : `CS.dijkstra w src v = CS.graphDist w src v` for every `v`.
-/

namespace CS

variable {V : Type*}

/-- A walk starting at `src` is represented by the list `p` of the vertices visited after
`src`; its endpoint is the last element of `p`, or `src` if `p` is empty. -/

theorem exampleGraphDist : graphDist exampleWeights 0 1 = 2 := by
  refine le_antisymm ?_ ?_
  · have hmem : ([2, 1] : List (Fin 3)) ∈ {p : List (Fin 3) | walkEnd 0 p = 1} := by
      simp [walkEnd]
    have h := iInf₂_le (f := fun p (_ : p ∈ {p : List (Fin 3) | walkEnd 0 p = 1}) =>
      walkWeight exampleWeights 0 p) _ hmem
    refine le_trans h (le_of_eq ?_)
    show exampleWeights 0 2 + (exampleWeights 2 1 + 0) = 2
    simp [exampleWeights, Matrix.cons_val]
    norm_num
  · have h := le_graphDist_of_potential exampleWeights examplePotential
      examplePotential_feasible 0 1
    simpa [examplePotential] using h

/-- Dijkstra's algorithm returns the value `2` on the example. -/
