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

theorem stepD_spec (w : V → V → ℕ∞) (S : Finset V) (d : V → ℕ∞) (h : (univ \ S).Nonempty) :
    ∃ u, u ∉ S ∧ (∀ v ∉ S, d u ≤ d v) ∧
      stepD w (S, d) = (insert u S, fun v => d v ⊓ (d u + w u v)) := by
  classical
  obtain ⟨hmem, hmin⟩ := ((univ \ S).exists_min_image d h).choose_spec
  refine ⟨((univ \ S).exists_min_image d h).choose, (mem_sdiff.1 hmem).2, ?_, ?_⟩
  · intro v hv
    exact hmin v (mem_sdiff.2 ⟨mem_univ v, hv⟩)
  · simp only [stepD, dif_pos h]

omit [Fintype V] in
/-- Key step: if `u` is an unsettled vertex of minimal tentative distance, then every walk
from `src` ending outside `S` costs at least `d u`. -/
