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

theorem euler : Fintype.card (Fin 4) + Fintype.card (Fin 4)
    = Fintype.card (⊤ : SimpleGraph (Fin 4)).edgeSet + 2 :=
  Chem.euler_polyhedron edgeEquiv star_le_top star_isTree star_le_top star_isTree tree_cotree

end Tetrahedron

/-- **Fullerene cages have exactly 12 pentagonal faces.**

If a cage is trivalent (`3 * V = 2 * E`, every carbon atom has three neighbours) and every
face is a pentagon or a hexagon (`F = p + h` and `5 * p + 6 * h = 2 * E`), then Euler's
formula `V + F = E + 2` forces `p = 12`. -/
