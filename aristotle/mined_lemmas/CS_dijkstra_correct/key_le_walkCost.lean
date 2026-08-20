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

theorem key_le_walkCost (w : V → V → ℕ∞) (src : V) (S : Finset V) (d : V → ℕ∞)
    (hd : ∀ v, d v = tent w src S v) (u : V) (hmin : ∀ v ∉ S, d u ≤ d v) :
    ∀ l : List V, l.getLastD src ∉ S → d u ≤ walkCost w src l := by
  intro l
  induction l using List.reverseRecOn with
  | nil =>
      intro hsrc
      have := hmin src (by simpa using hsrc)
      simpa [hd src, tent] using this
  | append_singleton l v ih =>
      intro hv
      rw [List.getLastD_concat] at hv
      rw [walkCost_append]
      set z := l.getLastD src with hz
      by_cases hzS : z ∈ S
      · -- the last edge leaves a settled vertex
        have h1 : sdist w src z ≤ walkCost w src l := sdist_le_walkCost w src z hz.symm
        have h2 : tent w src S v ≤ sdist w src z + w z v :=
          le_trans inf_le_right (Finset.inf_le hzS)
        calc d u ≤ d v := hmin v (by simpa using hv)
          _ = tent w src S v := hd v
          _ ≤ sdist w src z + w z v := h2
          _ ≤ walkCost w src l + w z v := by gcongr
      · exact le_trans (ih hzS) (by simp)

/-- The invariant maintained by Dijkstra's algorithm. -/
