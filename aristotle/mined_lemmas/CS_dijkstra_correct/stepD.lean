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

noncomputable def stepD (w : V → V → ℕ∞) (st : Finset V × (V → ℕ∞)) : Finset V × (V → ℕ∞) :=
  if h : (univ \ st.1).Nonempty then
    let u := ((univ \ st.1).exists_min_image st.2 h).choose
    (insert u st.1, fun v => st.2 v ⊓ (st.2 u + w u v))
  else st

/-- The state of Dijkstra's algorithm from source `src` after `n` steps. -/
