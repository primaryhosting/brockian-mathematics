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

lemma distS_univ (w : V → V → ℝ≥0∞) (s t : V) :
    distS w (Finset.univ : Finset V) s t = spDist w s t := by
  refine le_antisymm ?_ (spDist_le_distS w _ s t)
  refine sInf_le_sInf ?_
  rintro b ⟨l, hl, hc⟩
  exact ⟨l, hl, interIn_univ, hc⟩

end Fintype

/-! ## The two key lemmas -/

section Key

variable [DecidableEq V]

/-- **Extraction is correct.**  If the tentative distances `d` are the `S`-restricted
distances and `u` is an unvisited vertex minimizing `d`, then `d u` is already the true
shortest-path distance.  This is where nonnegativity of the weights is used: the part of
a path lying beyond the first unvisited vertex it meets can only increase its cost. -/
