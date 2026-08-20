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

lemma gdist_le_cost {w : V → V → ℝ≥0∞} {s t : V} {l : List V} (hl : endpt s l = t) :
    gdist w s t ≤ cost w s l :=
  iInf_le_of_le l (iInf_le_of_le hl le_rfl)

/-- The distance from a vertex to itself is `0` (the empty walk). -/
