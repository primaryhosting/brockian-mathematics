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

lemma step_spec (w : V → V → ℝ≥0∞) (st : DState V) (h : (st.visitedᶜ : Finset V).Nonempty) :
    ∃ u : V, u ∉ st.visited ∧ (∀ y ∉ st.visited, st.dist u ≤ st.dist y) ∧
      step w st = ⟨insert u st.visited, fun v => st.dist v ⊓ (st.dist u + w u v)⟩ := by
  obtain ⟨hmem, hmin⟩ := ((st.visitedᶜ : Finset V).exists_min_image st.dist h).choose_spec
  refine ⟨_, by simpa using hmem, fun y hy => hmin y (by simpa using hy), ?_⟩
  simp only [step, dif_pos h]

