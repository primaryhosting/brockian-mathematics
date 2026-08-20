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

lemma exists_good_prefix (w : V → V → ℝ≥0∞) (S : Finset V) :
    ∀ (s : V) (l : List V), endpt s l ∉ S →
      ∃ p : List V, Restr S s p ∧ endpt s p ∉ S ∧ cost w s p ≤ cost w s l := by
  intro s l
  induction l generalizing s with
  | nil => exact fun h => ⟨[], trivial, h, le_rfl⟩
  | cons x l ih =>
      intro h
      by_cases hs : s ∈ S
      · rcases ih x (by simpa using h) with ⟨p, hp1, hp2, hp3⟩
        refine ⟨x :: p, ⟨hs, hp1⟩, by simpa using hp2, ?_⟩
        simp only [cost_cons]
        exact add_le_add le_rfl hp3
      · exact ⟨[], trivial, hs, by simp⟩

/-- **Key step of Dijkstra's algorithm.** If `u ∉ S` minimises the `S`-restricted distance
among all vertices outside `S`, then this restricted distance is the true distance. -/
