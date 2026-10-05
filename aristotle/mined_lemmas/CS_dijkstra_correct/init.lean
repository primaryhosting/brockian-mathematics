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

noncomputable def init (s : V) : Finset V × (V → ℝ≥0∞) :=
  (∅, fun v => if v = s then 0 else ⊤)

/-- Dijkstra's algorithm: iterate `step` once per vertex, starting from `init s`. -/
