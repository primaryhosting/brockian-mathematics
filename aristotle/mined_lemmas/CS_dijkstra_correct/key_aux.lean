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

lemma key_aux (w : V → V → ℝ≥0∞) (s : V) (st : DState V) (h : Inv w s st) :
    ∀ (l : List V) (a : V), a ∈ st.visited → l.getLastD a ∉ st.visited →
      ∃ y ∉ st.visited, st.dist y ≤ sdist w s a + walkCost w a l := by
  intro l
  induction l with
  | nil => intro a ha hend; exact absurd (by simpa using ha) hend
  | cons b l ih =>
      intro a ha hend
      rw [List.getLastD_cons] at hend
      by_cases hb : b ∈ st.visited
      · obtain ⟨y, hy, hle⟩ := ih b hb hend
        refine ⟨y, hy, hle.trans ?_⟩
        have h1 : sdist w s b ≤ sdist w s a + w a b := sdist_triangle w s a b
        calc sdist w s b + walkCost w b l
            ≤ (sdist w s a + w a b) + walkCost w b l := by gcongr
          _ = sdist w s a + walkCost w a (b :: l) := by rw [walkCost, add_assoc]
      · refine ⟨b, hb, ?_⟩
        have h1 : st.dist b ≤ sdist w s a + w a b := inv_le_edge w s st h b hb a ha
        refine h1.trans ?_
        rw [walkCost, ← add_assoc]
        exact le_self_add

omit [Fintype V] in
/-- Any walk from `s` to an unvisited vertex costs at least the tentative distance of
some unvisited vertex. -/
