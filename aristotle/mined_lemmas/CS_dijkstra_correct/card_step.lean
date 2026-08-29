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

lemma card_step (w : V → V → ℝ≥0∞) (st : DState V) (k : ℕ)
    (h : st.visited = Finset.univ ∨ st.visited.card = k) :
    (step w st).visited = Finset.univ ∨ (step w st).visited.card = k + 1 := by
  by_cases hne : (st.visitedᶜ : Finset V).Nonempty
  · obtain ⟨u, hu, -, hstep⟩ := step_spec w st hne
    have hcard : st.visited.card = k := by
      rcases h with h | h
      · exact absurd (h ▸ Finset.mem_univ u) hu
      · exact h
    right
    rw [hstep]
    simp only
    rw [Finset.card_insert_of_notMem hu, hcard]
  · left
    rw [step_of_not_nonempty w st hne]
    have : (st.visitedᶜ : Finset V) = ∅ := Finset.not_nonempty_iff_eq_empty.1 hne
    simpa using congrArg (fun t : Finset V => tᶜ) this

