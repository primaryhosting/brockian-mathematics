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

variable {V : Type*}

/-! ## Graphs, walks and shortest-path distance

A weighted digraph on the vertex type `V` is given by a weight function
`w : V → V → ℝ≥0∞`.  Weights are nonnegative by construction (this is exactly the
hypothesis Dijkstra's algorithm needs), and the value `⊤` encodes the absence of an edge. -/

/-- `walkCost w a l` is the total weight of the walk that starts at `a` and then visits
the vertices of `l` in order. -/

lemma sdist_edge (w : V → V → ℝ≥0∞) (s u v : V) : sdist w s v ≤ sdist w s u + w u v := by
  have hrw : sdist w s u + w u v
      = ⨅ l : List V, ⨅ _ : l.getLastD s = u, (walkCost w s l + w u v) := by
    rw [sdist, ENNReal.iInf_add]
    exact iInf_congr fun l => ENNReal.iInf_add
  rw [hrw]
  refine le_iInf fun l => le_iInf fun hl => ?_
  have hcost : walkCost w s (l ++ [v]) = walkCost w s l + w u v := by
    rw [walkCost_append, hl]
    simp [walkCost]
  have hlast : (l ++ [v]).getLastD s = v := by simp
  have h := sdist_le_walkCost w s v (l ++ [v]) hlast
  rwa [hcost] at h


/-- The distance is at most the weight of the direct edge. -/
