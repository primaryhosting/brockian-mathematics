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

lemma restDist_append_edge (w : V → V → ℝ≥0∞) (src : V) (S : Finset V) {a : V} (ha : a ∈ S)
    (v : V) : restDist w src S v ≤ restDist w src S a + w a v := by
  have hrw : restDist w src S a + w a v
      = ⨅ p, ⨅ _ : p ∈ walks src S a, (walkWeight w src p + w a v) := by
    rw [restDist]; simp only [ENNReal.iInf_add]
  rw [hrw]
  refine le_iInf₂ (fun p hp => ?_)
  have hend : walkEnd src p = a := hp.1
  have hmem : p ++ [v] ∈ walks src S v := by
    refine ⟨walkEnd_concat src v p, ?_⟩
    intro x hx
    have hx' : x ∈ src :: p := by
      have hd : (src :: (p ++ [v])).dropLast = src :: p := by
        rw [← List.cons_append]; exact List.dropLast_concat
      rwa [hd] at hx
    exact mem_of_dropLast_mem hp.2 (by rw [hend]; exact ha) x hx'
  calc restDist w src S v ≤ walkWeight w src (p ++ [v]) := restDist_le_of_mem w src S v hmem
    _ = walkWeight w src p + w a v := by rw [walkWeight_concat, hend]

