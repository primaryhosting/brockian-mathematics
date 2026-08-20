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

lemma edgeEquiv_coe (e : (⊤ : SimpleGraph (Fin 4)).edgeSet) :
    (edgeEquiv e : Sym2 (Fin 4)) = cmap (e : Sym2 (Fin 4)) := rfl

/-- The tree–cotree condition: an edge of the tetrahedron avoids the vertex `0` exactly
when the dual edge it corresponds to meets the face `0`. -/
