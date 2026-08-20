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

theorem dijkstra_correct (w : V → V → ℝ≥0∞) (s v : V) : dijkstra w s v = sdist w s v := by
  have hinv := inv_iterate w s (Fintype.card V)
  have hcard := card_iterate w s (Fintype.card V) le_rfl
  have huniv : ((dijkstraStep w)^[Fintype.card V] (initState s)).1 = Finset.univ :=
    Finset.eq_univ_of_card _ hcard
  exact hinv.2.1 v (huniv ▸ Finset.mem_univ v)

end CS

#print axioms CS.dijkstra_correct

