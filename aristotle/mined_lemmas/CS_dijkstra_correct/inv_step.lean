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

lemma inv_step (w : V → V → ℝ≥0∞) (s : V) (st : DState V) (h : Inv w s st) :
    Inv w s (step w st) := by
  by_cases hne : (st.visitedᶜ : Finset V).Nonempty
  · obtain ⟨u, hu, hmin, hstep⟩ := step_spec w st hne
    have hdu : st.dist u = sdist w s u := dist_chosen w s st h u hu hmin
    rw [hstep]
    constructor
    · intro x hx
      simp only [Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · simp only
        rw [hdu]
        exact inf_eq_left.2 le_self_add
      · have hxx : st.dist x = sdist w s x := h.1 x hx
        simp only
        rw [hxx, hdu]
        exact inf_eq_left.2 (sdist_triangle w s u x)
    · intro v hv
      simp only [Finset.mem_insert, not_or] at hv
      obtain ⟨hvu, hvS⟩ := hv
      simp only
      rw [h.2 v hvS, hdu, Finset.iInf_insert]
      rw [inf_assoc, inf_comm (sdist w s u + w u v) _]
  · rw [step_of_not_nonempty w st hne]
    exact h

