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

lemma pathCost_toENN_of_not_edgesIn {adj : V → V → Prop} {wr : V → V → ℝ}
    (x : V) (l : List V) (h : ¬ edgesIn adj x l) :
    pathCost (toENN adj wr) x l = ⊤ := by
  induction l generalizing x with
  | nil => exact absurd trivial h
  | cons y l ih =>
    by_cases hadj : adj x y
    · have h' : ¬ edgesIn adj y l := fun hc => h ⟨hadj, hc⟩
      rw [pathCost, ih y h', add_top]
    · rw [pathCost, toENN, if_neg hadj, top_add]

/-- **Correctness of Dijkstra's algorithm, for real nonnegative edge weights.**
On a finite digraph with adjacency relation `adj` and nonnegative real edge weights `wr`,
Dijkstra's algorithm returns the infimum of the real costs of the paths from `s` to `t`
(and `⊤` when there is no such path). -/
