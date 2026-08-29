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

lemma inv_ge (w : V → V → ℝ≥0∞) (s : V) (st : DState V) (h : Inv w s st) (v : V) :
    sdist w s v ≤ st.dist v := by
  by_cases hv : v ∈ st.visited
  · rw [h.1 v hv]
  · rw [h.2 v hv]
    refine le_inf ?_ (le_iInf₂ fun x _ => sdist_triangle w s x v)
    by_cases hvs : v = s
    · subst hvs; simp [sdist_self]
    · simp [hvs]

omit [Fintype V] in
/-- Auxiliary induction: any walk that starts inside the visited set and leaves it
witnesses a tentative distance of an unvisited vertex. -/
