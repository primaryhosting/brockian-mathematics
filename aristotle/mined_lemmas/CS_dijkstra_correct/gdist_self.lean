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

lemma gdist_self (w : V → V → ℝ≥0∞) (s : V) : gdist w s s = 0 :=
  le_antisymm (by simpa [wcost, endpt] using gdist_le_of_walk w s ([] : List V)) (zero_le _)

omit [Fintype V] [DecidableEq V] in
/-- If all edges out of `S` have been relaxed, then the tentative distance of the endpoint
of a walk whose internal vertices lie in `S` is at most the current distance of its start
plus the weight of that walk. -/
