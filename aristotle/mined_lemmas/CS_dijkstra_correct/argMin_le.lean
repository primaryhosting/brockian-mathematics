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

lemma argmin_le (S : Finset V) (d : V → ℝ≥0∞) (h : S.Nonempty) :
    ∀ y ∈ S, d (argmin S d h) ≤ d y :=
  (S.exists_min_image d h).choose_spec.2

/-- One iteration of Dijkstra's algorithm: settle the closest unsettled vertex `u`
and relax all edges out of `u`. -/
