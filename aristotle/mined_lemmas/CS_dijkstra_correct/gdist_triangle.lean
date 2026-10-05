import Mathlib

/-!
# Dijkstra Correct
Category: Computer Science
Target: CS.dijkstra_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

open scoped ENNReal

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `wcost w u l` is the total weight of the walk that starts at `u` and visits the
vertices of `l` in order. -/

lemma gdist_triangle (w : V → V → ℝ≥0∞) (s u v : V) :
    gdist w s v ≤ gdist w s u + w u v := by
  simp only [gdist]
  rw [ENNReal.sInf_add]
  refine le_iInf₂ ?_
  rintro c ⟨l, hl, rfl⟩
  have h1 : gdist w s (endpt s (l ++ [v])) ≤ wcost w s (l ++ [v]) := gdist_le_of_walk w s _
  rw [endpt_append_singleton, wcost_append_singleton, hl] at h1
  exact h1

omit [Fintype V] [DecidableEq V] in
