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

noncomputable def argmin (S : Finset V) (d : V → ℝ≥0∞) (h : S.Nonempty) : V :=
  (S.exists_min_image d h).choose

omit [Fintype V] [DecidableEq V] in
