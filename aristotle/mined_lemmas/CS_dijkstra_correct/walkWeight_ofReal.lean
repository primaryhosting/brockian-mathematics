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

lemma walkWeight_ofReal (wr : V → V → ℝ) (hw : ∀ u v, 0 ≤ wr u v) (a : V) (p : List V) :
    walkWeight (fun u v => ENNReal.ofReal (wr u v)) a p
      = ENNReal.ofReal (realWalkWeight wr a p) := by
  induction p generalizing a with
  | nil => simp [walkWeight, realWalkWeight]
  | cons x q ih =>
      have hw1 : walkWeight (fun u v => ENNReal.ofReal (wr u v)) a (x :: q)
          = ENNReal.ofReal (wr a x) + walkWeight (fun u v => ENNReal.ofReal (wr u v)) x q := rfl
      rw [hw1, ih x, realWalkWeight,
        ENNReal.ofReal_add (hw a x) (realWalkWeight_nonneg wr hw x q)]

/-- **Correctness of Dijkstra's algorithm for nonnegative real weights**: the algorithm run on
the weights `ENNReal.ofReal ∘ wr` returns, at every vertex `v`, the infimum of the weights of
all walks from the source to `v`. -/
