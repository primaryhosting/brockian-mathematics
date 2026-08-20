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

lemma argMin_le (d : V → ℝ≥0∞) (x : V) (l : List V) :
    ∀ v ∈ x :: l, d (argMin d x l) ≤ d v := by
  induction l generalizing x with
  | nil =>
    intro v hv
    rw [List.mem_singleton] at hv
    simp [argMin, hv]
  | cons y l ih =>
    intro v hv
    rw [argMin]
    have hzx : d (if d y < d x then y else x) ≤ d x := by
      by_cases hc : d y < d x
      · rw [if_pos hc]; exact hc.le
      · rw [if_neg hc]
    have hzy : d (if d y < d x then y else x) ≤ d y := by
      by_cases hc : d y < d x
      · rw [if_pos hc]
      · rw [if_neg hc]; exact not_lt.mp hc
    have hself : d (argMin d (if d y < d x then y else x) l)
        ≤ d (if d y < d x then y else x) := ih _ _ List.mem_cons_self
    rcases List.mem_cons.mp hv with rfl | hv'
    · exact hself.trans hzx
    · rcases List.mem_cons.mp hv' with rfl | hv''
      · exact hself.trans hzy
      · exact ih _ v (List.mem_cons_of_mem _ hv'')

section Fintype

variable [Fintype V]

