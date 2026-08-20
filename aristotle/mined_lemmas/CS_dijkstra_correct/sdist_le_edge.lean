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

lemma sdist_le_edge (w : V → V → ℝ≥0∞) (s v : V) : sdist w s v ≤ w s v := by
  simpa [walkCost] using sdist_le_walkCost w s v [v] (by simp)

/-- Sanity check: with no edges at all, every vertex other than the source is at
distance `⊤`, i.e. `sdist` is not degenerate. -/
example {V : Type*} (s v : V) (h : v ≠ s) : sdist (fun _ _ => (⊤ : ℝ≥0∞)) s v = ⊤ := by
  refine le_antisymm le_top (le_sdist _ _ _ _ ?_)
  intro l hl
  match l with
  | [] => exact absurd hl.symm h
  | x :: t => simp [walkCost]

/-- Sanity check: if every edge has weight at least `1`, then every vertex other than the
source is at distance at least `1`. -/
example (w : V → V → ℝ≥0∞) (h1 : ∀ x y, 1 ≤ w x y) (s v : V) (h : v ≠ s) :
    1 ≤ sdist w s v := by
  refine le_sdist _ _ _ _ ?_
  intro l hl
  match l with
  | [] => exact absurd hl.symm h
  | x :: t =>
      show (1 : ℝ≥0∞) ≤ w s x + walkCost w x t
      exact le_trans (h1 s x) le_self_add

/-! ## The algorithm -/

variable [Fintype V] [DecidableEq V]

/-- The unvisited vertex with the smallest tentative distance (the vertex that Dijkstra's
algorithm extracts from the priority queue). -/
