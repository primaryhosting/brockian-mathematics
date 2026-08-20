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

lemma star_reach (x : Fin 4) : star.Reachable 0 x := by
  rcases eq_or_ne (0 : Fin 4) x with rfl | hx
  · rfl
  · exact SimpleGraph.Adj.reachable ((star_adj 0 x).2 ⟨hx, Or.inl rfl⟩)

