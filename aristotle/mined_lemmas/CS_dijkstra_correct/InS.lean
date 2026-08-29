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

def InS (S : Finset V) : V → List V → Prop
  | _, [] => True
  | u, v :: l => u ∈ S ∧ InS S v l

/-- The invariants maintained by Dijkstra's algorithm: `S` is the set of settled
vertices and `d` the current tentative distances. -/
structure Inv (w : V → V → ℝ≥0∞) (s : V) (S : Finset V) (d : V → ℝ≥0∞) : Prop where
  zero : d s = 0
  ge : ∀ v, gdist w s v ≤ d v
  visited : ∀ x ∈ S, d x = gdist w s x
  order : ∀ x ∈ S, ∀ y ∉ S, d x ≤ d y
  relax : ∀ x ∈ S, ∀ y, d y ≤ d x + w x y

/-- The vertex of `S` with minimal tentative distance. -/
