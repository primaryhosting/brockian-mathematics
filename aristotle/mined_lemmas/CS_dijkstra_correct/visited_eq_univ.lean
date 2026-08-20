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

theorem visited_eq_univ (w : V → V → ℕ∞) (src : V) :
    (dijkstraAux w src (Fintype.card V)).1 = univ := by
  rcases card_visited w src (Fintype.card V) with h | h
  · exact h
  · exact Finset.eq_univ_of_card _ (le_antisymm (Finset.card_le_univ _) h)

/-- **Correctness of Dijkstra's algorithm.**  On a finite digraph with nonnegative weights
`w : V → V → ℕ∞` (`⊤` meaning "no edge"), the value computed by Dijkstra's algorithm from
`src` at `t` is the shortest-path distance from `src` to `t`, i.e. the infimum of the costs
of all walks from `src` to `t`. -/
