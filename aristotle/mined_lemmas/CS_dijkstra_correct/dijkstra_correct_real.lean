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

theorem dijkstra_correct_real [Fintype V] [DecidableEq V] (wr : V → V → ℝ)
    (hw : ∀ u v, 0 ≤ wr u v) (src v : V) :
    dijkstra (fun u v => ENNReal.ofReal (wr u v)) src v
      = ⨅ p ∈ {p : List V | walkEnd src p = v}, ENNReal.ofReal (realWalkWeight wr src p) := by
  rw [dijkstra_correct, graphDist]
  exact iInf_congr fun p => iInf_congr fun _ => walkWeight_ofReal wr hw src p

end CS

