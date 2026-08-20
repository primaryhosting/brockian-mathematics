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

lemma rdist_empty [DecidableEq V] (w : V → V → ℝ≥0∞) (s t : V) :
    rdist w (∅ : Finset V) s t = if t = s then 0 else ⊤ := by
  by_cases h : t = s
  · subst h; simp [rdist_self]
  · simp only [h, if_false]
    rw [eq_top_iff]
    exact le_rdist fun l hl hr => by
      rw [Restr_empty_eq_nil s l hr] at hl; exact absurd hl.symm h

