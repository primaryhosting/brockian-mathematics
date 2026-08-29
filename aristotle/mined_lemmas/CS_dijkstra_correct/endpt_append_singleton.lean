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

lemma endpt_append_singleton (u : V) (l : List V) (v : V) : endpt u (l ++ [v]) = v := by
  induction l generalizing u with
  | nil => simp [endpt]
  | cons a l ih => simp [endpt, ih]

omit [Fintype V] [DecidableEq V] in
