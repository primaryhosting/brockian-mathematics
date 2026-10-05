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

lemma gdist_le_of_walk (w : V → V → ℝ≥0∞) (s : V) (l : List V) :
    gdist w s (endpt s l) ≤ wcost w s l :=
  sInf_le ⟨l, rfl, rfl⟩

omit [Fintype V] [DecidableEq V] in
