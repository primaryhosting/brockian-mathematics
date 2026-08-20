import Mathlib

/-!
# Dijkstra Correct
Category: Computer Science
Target: CS.dijkstra_correct
Statement: Dijkstra's algorithm computes shortest-path distances on nonnegative-weight graphs.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open scoped ENNReal

namespace CS

variable {V : Type*}

/-! ## Walks, their costs, and shortest-path distances

A weighted directed graph on the vertex type `V` is given by a weight function
`w : V → V → ℝ≥0∞`.  Values in `ℝ≥0∞` are automatically nonnegative (this is the
"nonnegative weights" hypothesis), and `w u v = ⊤` encodes the absence of an edge
from `u` to `v`.

A walk starting at `s` is described by the list `l` of the vertices it visits after `s`. -/

/-- The endpoint of the walk that starts at `s` and visits the vertices of `l` in order. -/

lemma rdist_extend (w : V → V → ℝ≥0∞) {S : Finset V} {z : V} (hz : z ∈ S) (s v : V) :
    rdist w S s v ≤ rdist w S s z + w z v := by
  rw [rdist_add]
  refine le_iInf fun l => le_iInf fun hl => le_iInf fun hr => ?_
  have hend : endpt s (l ++ [v]) = v := by rw [endpt_append]; simp
  have hres : Restr S s (l ++ [v]) := by
    rw [Restr_append]
    exact ⟨hr, by simp [hl, hz]⟩
  have := rdist_le_cost (w := w) hend hres
  rwa [cost_append, hl, cost_cons, cost_nil, add_zero] at this

/-- If a walk from `s` ends outside `S`, it has a prefix that stays inside `S` (except for
its endpoint), ends outside `S`, and costs no more. -/
