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

theorem card_visited (w : V → V → ℕ∞) (src : V) (n : ℕ) :
    (dijkstraAux w src n).1 = univ ∨ n ≤ (dijkstraAux w src n).1.card := by
  induction n with
  | zero => right; simp
  | succ n ih =>
      have hstep : dijkstraAux w src (n + 1) = stepD w ((dijkstraAux w src n).1,
          (dijkstraAux w src n).2) := by simp [dijkstraAux]
      rcases ih with h | h
      · left
        have : ¬ (univ \ (dijkstraAux w src n).1).Nonempty := by
          simp [h]
        rw [hstep, show stepD w ((dijkstraAux w src n).1, (dijkstraAux w src n).2)
          = ((dijkstraAux w src n).1, (dijkstraAux w src n).2) by simp [stepD, this]]
        exact h
      · by_cases hS : (univ \ (dijkstraAux w src n).1).Nonempty
        · obtain ⟨u, huS, _, heq⟩ := stepD_spec w (dijkstraAux w src n).1
            (dijkstraAux w src n).2 hS
          right
          rw [hstep, heq]
          simpa [Finset.card_insert_of_notMem huS] using h
        · left
          have : univ \ (dijkstraAux w src n).1 = ∅ := Finset.not_nonempty_iff_eq_empty.1 hS
          have h2 : (dijkstraAux w src n).1 = univ := by
            have := Finset.sdiff_eq_empty_iff_subset.1 this
            exact Finset.eq_univ_of_forall fun v => this (mem_univ v)
          rw [hstep, show stepD w ((dijkstraAux w src n).1, (dijkstraAux w src n).2)
            = ((dijkstraAux w src n).1, (dijkstraAux w src n).2) by simp [stepD, hS]]
          exact h2

