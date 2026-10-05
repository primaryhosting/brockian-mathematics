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

lemma wcost_append_singleton (w : V → V → ℝ≥0∞) (u : V) (l : List V) (v : V) :
    wcost w u (l ++ [v]) = wcost w u l + w (endpt u l) v := by
  induction l generalizing u with
  | nil => simp [wcost, endpt]
  | cons a l ih => simp [wcost, endpt, ih, add_assoc]

omit [Fintype V] [DecidableEq V] in
