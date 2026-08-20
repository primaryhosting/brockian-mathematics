import Mathlib

/-!
# Euler Polyhedron
Category: Chemistry
Target: Chem.euler_polyhedron
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
NOTE ON FILE LAYOUT: Lean 4 requires `import` commands to come first in a file, so the
mandated header block appears immediately after the single `import Mathlib` line, with its
text reproduced verbatim.
-/

namespace Chem

open SimpleGraph

section TreeCotree

variable {α : Type*} {G H : SimpleGraph α}

/-- The edges of a subgraph `H ≤ G`, viewed inside the edge set of `G`, biject with the
edges of `H`. -/

lemma star_card_edges : Nat.card star.edgeSet = 3 := by
  have h := star.sum_degrees_eq_twice_card_edges
  have h2 : ∑ v : Fin 4, star.degree v = 6 := by decide
  rw [h2] at h
  rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]
  omega

