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

def cf : Fin 4 → Fin 4 → Sym2 (Fin 4) :=
  ![![s(0,0), s(2,3), s(1,3), s(1,2)],
    ![s(2,3), s(1,1), s(0,3), s(0,2)],
    ![s(1,3), s(0,3), s(2,2), s(0,1)],
    ![s(1,2), s(0,2), s(0,1), s(3,3)]]

