import Mathlib

/-!
# Dijkstra Correct
Category: Computer Science
Target: CS.dijkstra_correct
Statement: Dijkstra's algorithm computes shortest-path distances on nonnegative-weight graphs.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open scoped ENNReal

namespace CS

variable {V : Type*}

/-! ## Walks, their costs, and shortest-path distances

A weighted directed graph on the vertex type `V` is given by a weight function
`w : V → V → ℝ≥0∞`.  Values in `ℝ≥0∞` are automatically nonnegative (this is the
"nonnegative weights" hypothesis), and `w u v = ⊤` encodes the absence of an edge
from `u` to `v`.

A walk starting at `s` is described by the list `l` of the vertices it visits after `s`. -/

/-- The endpoint of the walk that starts at `s` and visits the vertices of `l` in order. -/

lemma rdist_eq_gdist_of_min (w : V → V → ℝ≥0∞) (S : Finset V) (s u : V) (hu : u ∉ S)
    (hmin : ∀ v, v ∉ S → rdist w S s u ≤ rdist w S s v) :
    rdist w S s u = gdist w s u := by
  refine le_antisymm (le_gdist fun l hl => ?_) (gdist_le_rdist w S s u)
  have hend : endpt s l ∉ S := by rw [hl]; exact hu
  rcases exists_good_prefix w S s l hend with ⟨p, hp1, hp2, hp3⟩
  calc rdist w S s u ≤ rdist w S s (endpt s p) := hmin _ hp2
    _ ≤ cost w s p := rdist_le_cost rfl hp1
    _ ≤ cost w s l := hp3

variable [DecidableEq V]

/-- **The relaxation step is correct.** Adding the settled vertex `u` to `S` changes the
restricted distances exactly the way Dijkstra's relaxation does. -/
