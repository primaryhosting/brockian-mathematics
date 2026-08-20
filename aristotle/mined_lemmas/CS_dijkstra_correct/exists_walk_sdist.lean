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

theorem exists_walk_sdist (w : V → V → ℕ∞) (src t : V) :
    ∃ l : List V, l.getLastD src = t ∧ walkCost w src l = sdist w src t := by
  have hne : {c : ℕ∞ | ∃ l : List V, l.getLastD src = t ∧ walkCost w src l = c}.Nonempty :=
    ⟨walkCost w src [t], [t], rfl, rfl⟩
  simpa [sdist, Set.mem_setOf_eq] using csInf_mem hne

omit [Fintype V] [DecidableEq V] in
