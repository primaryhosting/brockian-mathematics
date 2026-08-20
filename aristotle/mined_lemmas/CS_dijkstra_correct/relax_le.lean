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

lemma relax_le [Fintype V] (w : V → V → ℝ≥0∞) (src : V) (S : Finset V) (d : V → ℝ≥0∞) (u : V)
    (hJ : ∀ v, d v = restDist w src S v) (hK : ∀ z ∈ S, d z = graphDist w src z)
    (hdu : d u = graphDist w src u) [DecidableEq V] :
    ∀ (p : List V) (v : V), p ∈ walks src (insert u S) v →
      min (d v) (d u + w u v) ≤ walkWeight w src p := by
  intro p
  induction p using List.reverseRecOn with
  | nil =>
      intro v hp
      have hv : src = v := hp.1
      subst hv
      have hds : d src = 0 := by rw [hJ, restDist_self]
      have h0 : walkWeight w src ([] : List V) = 0 := rfl
      rw [h0, ← hds]
      exact min_le_left _ _
  | append_singleton q x ih =>
      intro v hp
      obtain ⟨hpe, hpS⟩ := hp
      have hx : x = v := by rw [← hpe]; exact (walkEnd_concat src x q).symm
      subst hx
      have hdrop : (src :: (q ++ [x])).dropLast = src :: q := by
        rw [← List.cons_append]; exact List.dropLast_concat
      set z := walkEnd src q with hz
      have hzmem : z ∈ insert u S := hpS z (by rw [hdrop]; exact walkEnd_mem src q)
      have hq : q ∈ walks src (insert u S) z := by
        refine ⟨rfl, fun y hy => hpS y ?_⟩
        rw [hdrop]
        exact List.dropLast_subset _ hy
      have IH := ih z hq
      have hwq : walkWeight w src (q ++ [x]) = walkWeight w src q + w z x := by
        rw [walkWeight_concat]
      rcases Finset.mem_insert.mp hzmem with hzu | hzS
      · rw [hzu] at IH hwq
        have hu : min (d u) (d u + w u u) = d u := min_eq_left le_self_add
        rw [hu] at IH
        rw [hwq]
        exact le_trans (min_le_right _ _) (add_le_add IH le_rfl)
      · have hdz : d z ≤ d u + w u z := by
          rw [hK z hzS, hdu]; exact graphDist_append_edge w src u z
        rw [min_eq_left hdz] at IH
        rw [hwq]
        calc min (d x) (d u + w u x) ≤ d x := min_le_left _ _
          _ ≤ d z + w z x := by
              rw [hJ, hJ]; exact restDist_append_edge w src S hzS x
          _ ≤ walkWeight w src q + w z x := add_le_add IH le_rfl

