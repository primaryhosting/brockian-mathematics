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

lemma key_update (w : V → V → ℝ≥0∞) (S : Finset V) (s u : V) (d : V → ℝ≥0∞)
    (hd : ∀ v, d v = distS w S s v) (hz : ∀ z ∈ S, d z = spDist w s z)
    (hu : d u = spDist w s u) (v : V) :
    min (d v) (d u + w u v) = distS w (insert u S) s v := by
  have hB : ∀ (l : List V) (x : V) (c : ℝ≥0∞), interIn (insert u S) x l →
      min (d x) (d u + w u x) ≤ c → spDist w s x ≤ c →
      min (d (pathEnd x l)) (d u + w u (pathEnd x l)) ≤ c + pathCost w x l := by
    intro l
    induction l with
    | nil => intro x c _ h1 _; simpa [pathCost, pathEnd] using h1
    | cons y l ih =>
      intro x c hi h1 h2
      obtain ⟨hxS, hi'⟩ := hi
      have hdy : min (d y) (d u + w u y) ≤ c + w x y := by
        rcases Finset.mem_insert.mp hxS with rfl | hxS'
        · have hcu : d x ≤ c := by rw [hu]; exact h2
          exact (min_le_right _ _).trans (by gcongr)
        · have hdx : d x ≤ c := ((hz x hxS').le).trans h2
          have hy : d y ≤ c + w x y := by
            rw [hd y]
            calc distS w S s y ≤ distS w S s x + w x y := distS_edge (le_refl S) w s hxS' y
              _ = d x + w x y := by rw [hd x]
              _ ≤ c + w x y := by gcongr
          exact (min_le_left _ _).trans hy
      have hsy : spDist w s y ≤ c + w x y := (spDist_edge w s x y).trans (by gcongr)
      have h3 := ih y (c + w x y) hi' hdy hsy
      calc min (d (pathEnd x (y :: l))) (d u + w u (pathEnd x (y :: l)))
          = min (d (pathEnd y l)) (d u + w u (pathEnd y l)) := by rw [pathEnd_cons]
        _ ≤ c + w x y + pathCost w y l := h3
        _ = c + pathCost w x (y :: l) := by simp [pathCost, add_assoc]
  refine le_antisymm (le_distS ?_) (le_min ?_ ?_)
  · intro l hl hi
    have h0 : min (d s) (d u + w u s) ≤ 0 := by
      have hs : d s = 0 := by rw [hd s, distS_self]
      simp [hs]
    have := hB l s 0 hi h0 (by simp [spDist_self])
    rw [hl] at this
    simpa using this
  · rw [hd v]; exact distS_mono (Finset.subset_insert u S) w s v
  · rw [hd u]
    exact distS_edge (Finset.subset_insert u S) w s (Finset.mem_insert_self u S) v

end Key

/-! ## The algorithm -/

section Algorithm

variable [Fintype V] [DecidableEq V]

/-- One round of Dijkstra's algorithm, given the list of currently unvisited vertices:
extract an unvisited vertex `u` of minimal tentative distance, mark it visited,
and relax all edges out of `u`. -/
