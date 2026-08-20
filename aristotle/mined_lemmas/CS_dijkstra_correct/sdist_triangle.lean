import Mathlib

/-!
# Dijkstra Correct
Category: Computer Science
Target: CS.dijkstra_correct
Statement: Dijkstra's algorithm computes shortest-path distances on nonnegative-weight graphs.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Walks and shortest-path distances

A weighted digraph on the finite vertex type `V` is given by a weight function
`w : V → V → ℕ∞`, where `w u v = ⊤` encodes the absence of an edge from `u` to `v`.
All weights are nonnegative by construction. -/

/-- `walkCost w u l` is the total weight of the walk that starts at `u` and then visits
the vertices of `l` in order. -/

theorem sdist_triangle (w : V → V → ℕ∞) (src t v : V) :
    sdist w src v ≤ sdist w src t + w t v := by
  obtain ⟨l, hl, hc⟩ := exists_walk_sdist w src t
  have h : sdist w src v ≤ walkCost w src (l ++ [v]) := by
    refine sdist_le_walkCost w src v ?_
    simp
  rwa [walkCost_append, hl, hc] at h

/-! ## The algorithm

The state of the algorithm is a pair `(S, d)` where `S` is the set of settled vertices and
`d` the current tentative distance function.  One step picks an unsettled vertex `u` of
minimal tentative distance, settles it, and relaxes all edges out of `u`. -/

/-- One step of Dijkstra's algorithm. -/
