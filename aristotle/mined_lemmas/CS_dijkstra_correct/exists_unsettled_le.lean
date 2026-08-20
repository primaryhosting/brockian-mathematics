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

lemma exists_unsettled_le (w : V → V → ℝ≥0∞) (src : V) (S : Finset V) :
    ∀ (p : List V) (a : V) (c : ℝ≥0∞), restDist w src S a ≤ c → a ∈ S → walkEnd a p ∉ S →
      ∃ y ∉ S, restDist w src S y ≤ c + walkWeight w a p := by
  intro p
  induction p with
  | nil => intro a c _ haS hend; exact absurd haS (by simpa [walkEnd] using hend)
  | cons x q ih =>
      intro a c ha haS hend
      have h1 : restDist w src S x ≤ c + w a x :=
        le_trans (restDist_append_edge w src S haS x) (add_le_add ha le_rfl)
      have hw : walkWeight w a (x :: q) = w a x + walkWeight w x q := rfl
      by_cases hx : x ∈ S
      · have hend' : walkEnd x q ∉ S := by rwa [← walkEnd_cons a x q]
        obtain ⟨y, hy, hle⟩ := ih x (c + w a x) h1 hx hend'
        exact ⟨y, hy, by rw [hw, ← add_assoc]; exact hle⟩
      · exact ⟨x, hx, by rw [hw, ← add_assoc]; exact le_trans h1 le_self_add⟩

/-- The relaxation inequality: after settling `u`, the updated tentative distances are at most
the weight of any walk whose intermediate vertices lie in `insert u S`. -/
