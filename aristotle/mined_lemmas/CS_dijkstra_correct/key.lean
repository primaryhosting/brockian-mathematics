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

lemma key (w : V → V → ℝ≥0∞) (s : V) (st : DState V) (h : Inv w s st)
    (l : List V) (hl : l.getLastD s ∉ st.visited) :
    ∃ y ∉ st.visited, st.dist y ≤ walkCost w s l := by
  by_cases hs : s ∈ st.visited
  · have := key_aux w s st h l s hs hl
    simpa [sdist_self] using this
  · refine ⟨s, hs, ?_⟩
    have h0 : st.dist s ≤ 0 := by simpa using inv_le_init w s st h s hs
    exact h0.trans (zero_le _)

omit [Fintype V] in
/-- The vertex chosen by a step of Dijkstra's algorithm is settled correctly. -/
