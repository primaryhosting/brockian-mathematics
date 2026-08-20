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

@[simp] theorem walkCost_nil (w : V → V → ℕ∞) (u : V) : walkCost w u [] = 0 := rfl

omit [Fintype V] [DecidableEq V] in
