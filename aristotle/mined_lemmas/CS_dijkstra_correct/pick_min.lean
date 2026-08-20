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

lemma pick_min (d : V → ℝ≥0∞) (S : Finset V) (h : (Finset.univ \ S).Nonempty) :
    ∀ y ∉ S, d (pick d S h) ≤ d y := by
  intro y hy
  exact ((Finset.univ \ S).exists_min_image d h).choose_spec.2 y
    (Finset.mem_sdiff.mpr ⟨Finset.mem_univ y, hy⟩)

/-- One iteration of Dijkstra's main loop: extract the unvisited vertex `u` of minimal
tentative distance, mark it visited, and relax all edges leaving `u`. -/
