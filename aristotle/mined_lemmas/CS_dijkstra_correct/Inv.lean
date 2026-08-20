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

def Inv (w : V → V → ℝ≥0∞) (s : V) (S : Finset V) (d : V → ℝ≥0∞) : Prop :=
  (∀ v, sdist w s v ≤ d v) ∧
  (∀ x ∈ S, d x = sdist w s x) ∧
  (∀ v ∉ S, d v = min (if v = s then 0 else ⊤) (⨅ x ∈ S, sdist w s x + w x v))

omit [Fintype V] in
/-- Key step of the greedy argument: a walk from a visited vertex `a` to the extracted
vertex `u`, prefixed by a shortest walk from `s` to `a`, is at least as long as `d u`. -/
