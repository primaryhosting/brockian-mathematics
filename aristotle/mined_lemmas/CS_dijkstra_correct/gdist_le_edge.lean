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

lemma gdist_le_edge (w : V → V → ℝ≥0∞) (s t : V) : gdist w s t ≤ w s t := by
  simpa [endpt, wcost] using gdist_le_of_walk w s [t]

omit [Fintype V] [DecidableEq V] in
/-- Sanity check: if there are no edges at all, distinct vertices are at distance `⊤`. -/
