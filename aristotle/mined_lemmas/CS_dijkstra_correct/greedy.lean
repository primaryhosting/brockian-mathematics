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

lemma greedy (w : V → V → ℝ≥0∞) (s : V) (S : Finset V) (d : V → ℝ≥0∞)
    (hA : ∀ v, sdist w s v ≤ d v)
    (hC : ∀ v ∉ S, d v = min (if v = s then 0 else ⊤) (⨅ x ∈ S, sdist w s x + w x v))
    (u : V) (hu : u ∉ S) (hmin : ∀ y ∉ S, d u ≤ d y) : d u = sdist w s u := by
  refine le_antisymm ?_ (hA u)
  refine le_sdist w s u _ ?_
  intro l hl
  by_cases hs : s ∈ S
  · simpa using greedy_aux w s S d hC u hu hmin l s hs hl
  · have h0 : d s = 0 := by
      rw [hC s hs, if_pos rfl]
      exact min_eq_left (zero_le _)
    calc d u ≤ d s := hmin s hs
      _ = 0 := h0
      _ ≤ walkCost w s l := zero_le _

omit [Fintype V] in
/-- The invariant is preserved by "visit `u` and relax its outgoing edges". -/
