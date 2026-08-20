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

lemma card_step [Fintype V] [DecidableEq V] (w : V → V → ℝ≥0∞) (st : Finset V × (V → ℝ≥0∞)) :
    min (Fintype.card V) (st.1.card + 1) ≤ (step w st).1.card := by
  rw [step]
  split_ifs with hne
  · have huS : pick (Finset.univ \ st.1) hne st.2 ∉ st.1 := by
      have := pick_mem (Finset.univ \ st.1) hne st.2
      simpa [Finset.mem_sdiff] using this
    simp only [Finset.card_insert_of_notMem huS]
    exact min_le_right _ _
  · have : st.1 = Finset.univ := by
      rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at hne
      exact Finset.eq_univ_of_card _ (le_antisymm (Finset.card_le_univ _)
        (Finset.card_le_card hne))
    rw [this, Finset.card_univ]
    exact min_le_left _ _

