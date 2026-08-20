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

lemma key_extract (w : V → V → ℝ≥0∞) (S : Finset V) (s u : V) (d : V → ℝ≥0∞)
    (hd : ∀ v, d v = distS w S s v) (hu : u ∉ S) (hmin : ∀ y, y ∉ S → d u ≤ d y) :
    d u = spDist w s u := by
  have hA : ∀ (l : List V) (x : V) (c : ℝ≥0∞), distS w S s x ≤ c → pathEnd x l ∉ S →
      d u ≤ c + pathCost w x l := by
    intro l
    induction l with
    | nil =>
      intro x c hc hx
      calc d u ≤ d x := hmin x hx
        _ = distS w S s x := hd x
        _ ≤ c := hc
        _ ≤ c + pathCost w x [] := le_self_add
    | cons y l ih =>
      intro x c hc hx
      by_cases hxS : x ∈ S
      · have h1 : distS w S s y ≤ c + w x y :=
          (distS_edge (le_refl S) w s hxS y).trans (by gcongr)
        have h2 := ih y (c + w x y) h1 hx
        calc d u ≤ c + w x y + pathCost w y l := h2
          _ = c + pathCost w x (y :: l) := by simp [pathCost, add_assoc]
      · calc d u ≤ d x := hmin x hxS
          _ = distS w S s x := hd x
          _ ≤ c := hc
          _ ≤ c + pathCost w x (y :: l) := le_self_add
  refine le_antisymm (le_spDist ?_) ?_
  · intro l hl
    have := hA l s 0 (le_of_eq (distS_self w S s)) (by rw [hl]; exact hu)
    simpa using this
  · rw [hd u]; exact spDist_le_distS w S s u

/-- **Relaxation is correct.**  Relaxing the edges out of a vertex `u` whose tentative
distance is already final turns the `S`-restricted distances into the
`insert u S`-restricted distances. -/
