/-
# Dijkstra Correct
Category: Computer Science
Target: CS.dijkstra_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Dijkstra Correct
Category: Computer Science
Target: CS.dijkstra_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ENNReal

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace CS

universe u

variable {V : Type u}

/-! ## Walks and shortest-path distances

A weighted directed graph on the vertex type `V` is given by a weight function
`w : V → V → ℝ≥0∞`; the value `⊤` means "no edge", and all weights are nonnegative
by construction.  A walk starting at `a` is described by the list `l` of the vertices
it visits after `a`; its endpoint is `l.getLastD a`. -/

/-- The cost of the walk that starts at `a` and then visits the vertices of `l` in order. -/

lemma sdist_triangle (w : V → V → ℝ≥0∞) (s x t : V) :
    sdist w s t ≤ sdist w s x + w x t := by
  have h : sdist w s x + w x t
      = ⨅ l : List V, ⨅ _ : l.getLastD s = x, (walkCost w s l + w x t) := by
    rw [sdist, ENNReal.iInf_add]
    exact iInf_congr fun l => ENNReal.iInf_add
  rw [h]
  refine le_iInf fun l => le_iInf fun hl => ?_
  have hc : walkCost w s (l ++ [t]) = walkCost w s l + w x t := by
    rw [walkCost_append, hl]
  rw [← hc]
  exact sdist_le w s t _ (by simp)

/-- Sanity check that `sdist` is a genuine infimum over walks: in the edgeless graph
(all weights `⊤`) every vertex other than the source is at distance `⊤`. -/
example (s t : V) (hst : t ≠ s) : sdist (fun _ _ => (⊤ : ℝ≥0∞)) s t = ⊤ := by
  refine top_le_iff.mp (le_sdist _ s t ⊤ fun l hl => ?_)
  cases l with
  | nil => exact absurd (by simpa using hl.symm) hst
  | cons b l => simp [walkCost]

/-! ## The algorithm -/

/-- A state of Dijkstra's algorithm: the set of settled vertices together with the
current tentative distances. -/
structure DState (V : Type u) where
  visited : Finset V
  dist : V → ℝ≥0∞

variable [Fintype V] [DecidableEq V]

/-- One step of Dijkstra's algorithm: pick an unvisited vertex `u` of minimal tentative
distance, mark it visited, and relax all edges out of `u`. -/
