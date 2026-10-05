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

lemma argmin_mem (S : Finset V) (d : V → ℝ≥0∞) (h : S.Nonempty) : argmin S d h ∈ S :=
  (S.exists_min_image d h).choose_spec.1

omit [Fintype V] [DecidableEq V] in
