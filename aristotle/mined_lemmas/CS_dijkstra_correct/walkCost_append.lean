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

lemma walkCost_append (w : V → V → ℝ≥0∞) :
    ∀ (l m : List V) (a : V),
      walkCost w a (l ++ m) = walkCost w a l + walkCost w (l.getLastD a) m := by
  intro l
  induction l with
  | nil => intro m a; simp [walkCost]
  | cons x t ih =>
      intro m a
      simp only [List.cons_append, walkCost, ih, List.getLastD_cons, add_assoc]

