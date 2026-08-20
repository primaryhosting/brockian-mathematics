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

lemma inv_step (w : V → V → ℝ≥0∞) (s : V) (st : Finset V × (V → ℝ≥0∞))
    (h : Inv w s st.1 st.2) :
    Inv w s (dijkstraStep w st).1 (dijkstraStep w st).2 := by
  by_cases hne : (Finset.univ \ st.1).Nonempty
  · have hstep : dijkstraStep w st = (insert (pick st.2 st.1 hne) st.1,
        fun v => min (st.2 v) (st.2 (pick st.2 st.1 hne) + w (pick st.2 st.1 hne) v)) := by
      rw [dijkstraStep, dif_pos hne]
    rw [hstep]
    exact inv_relax w s st.1 st.2 h _ (pick_not_mem _ _ _) (pick_min _ _ _)
  · rw [dijkstraStep, dif_neg hne]
    exact h

omit [Fintype V] in
