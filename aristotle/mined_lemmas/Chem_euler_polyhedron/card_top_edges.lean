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

lemma card_top_edges : Fintype.card (⊤ : SimpleGraph (Fin 4)).edgeSet = 6 := by
  have h := (⊤ : SimpleGraph (Fin 4)).sum_degrees_eq_twice_card_edges
  have h2 : ∑ v : Fin 4, (⊤ : SimpleGraph (Fin 4)).degree v = 12 := by decide
  rw [h2, SimpleGraph.edgeFinset_card] at h
  omega

/-- The incidence bijection between edges of the tetrahedron and edges of its dual. -/
