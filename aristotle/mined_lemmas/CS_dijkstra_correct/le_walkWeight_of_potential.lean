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

lemma le_walkWeight_of_potential (w : V → V → ℝ≥0∞) (pot : V → ℝ≥0∞)
    (h : ∀ u v, pot v ≤ pot u + w u v) (a : V) (p : List V) :
    pot (walkEnd a p) ≤ pot a + walkWeight w a p := by
  induction p generalizing a with
  | nil => simp [walkEnd, walkWeight]
  | cons x q ih =>
      have hw : walkWeight w a (x :: q) = w a x + walkWeight w x q := rfl
      calc pot (walkEnd a (x :: q)) = pot (walkEnd x q) := by rw [walkEnd_cons]
        _ ≤ pot x + walkWeight w x q := ih x
        _ ≤ pot a + w a x + walkWeight w x q := add_le_add (h a x) le_rfl
        _ = pot a + walkWeight w a (x :: q) := by rw [hw, add_assoc]

/-- A feasible potential bounds the shortest-path distance from below. -/
