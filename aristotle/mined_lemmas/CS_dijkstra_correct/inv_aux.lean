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

theorem inv_aux (w : V → V → ℕ∞) (src : V) (n : ℕ) :
    Inv w src (dijkstraAux w src n).1 (dijkstraAux w src n).2 := by
  induction n with
  | zero => exact inv_init w src
  | succ n ih =>
      have : dijkstraAux w src (n + 1) = stepD w ((dijkstraAux w src n).1,
          (dijkstraAux w src n).2) := by
        simp [dijkstraAux]
      rw [this]
      exact inv_step w src _ _ ih

/-- After `n` steps, either all vertices are settled or at least `n` of them are. -/
