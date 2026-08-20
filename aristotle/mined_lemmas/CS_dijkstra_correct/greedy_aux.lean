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

lemma greedy_aux (w : V → V → ℝ≥0∞) (s : V) (S : Finset V) (d : V → ℝ≥0∞)
    (hC : ∀ v ∉ S, d v = min (if v = s then 0 else ⊤) (⨅ x ∈ S, sdist w s x + w x v))
    (u : V) (hu : u ∉ S) (hmin : ∀ y ∉ S, d u ≤ d y) :
    ∀ (l : List V) (a : V), a ∈ S → l.getLastD a = u → d u ≤ sdist w s a + walkCost w a l := by
  intro l
  induction l with
  | nil =>
      intro a ha hl
      simp only [List.getLastD_nil] at hl
      exact absurd (hl ▸ ha) hu
  | cons x t ih =>
      intro a ha hl
      rw [List.getLastD_cons] at hl
      have hcost : walkCost w a (x :: t) = w a x + walkCost w x t := rfl
      by_cases hx : x ∈ S
      · calc d u ≤ sdist w s x + walkCost w x t := ih x hx hl
          _ ≤ (sdist w s a + w a x) + walkCost w x t := by gcongr; exact sdist_edge w s a x
          _ = sdist w s a + walkCost w a (x :: t) := by rw [hcost, add_assoc]
      · have hiInf : (⨅ y ∈ S, sdist w s y + w y x) ≤ sdist w s a + w a x :=
          iInf₂_le_of_le a ha le_rfl
        have hdx : d x ≤ sdist w s a + w a x := by
          rw [hC x hx]
          exact le_trans (min_le_right _ _) hiInf
        calc d u ≤ d x := hmin x hx
          _ ≤ sdist w s a + w a x := hdx
          _ ≤ sdist w s a + walkCost w a (x :: t) := by
              rw [hcost]
              exact add_le_add le_rfl le_self_add

omit [Fintype V] in
/-- The greedy choice is correct: the extracted vertex already has its final distance. -/
