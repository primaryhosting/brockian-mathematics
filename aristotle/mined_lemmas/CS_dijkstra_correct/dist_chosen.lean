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

lemma dist_chosen (w : V → V → ℝ≥0∞) (s : V) (st : DState V) (h : Inv w s st)
    (u : V) (hu : u ∉ st.visited) (hmin : ∀ y ∉ st.visited, st.dist u ≤ st.dist y) :
    st.dist u = sdist w s u := by
  refine le_antisymm ?_ (inv_ge w s st h u)
  refine le_sdist w s u _ fun l hl => ?_
  obtain ⟨y, hy, hle⟩ := key w s st h l (by rw [hl]; exact hu)
  exact (hmin y hy).trans hle

/-- Description of a step when there is still an unvisited vertex. -/
