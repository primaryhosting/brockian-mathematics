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

lemma cmap_notDiag (e : Sym2 (Fin 4)) : ¬ (cmap e).IsDiag ↔ ¬ e.IsDiag := by
  induction e using Sym2.ind with
  | _ a b => fin_cases a <;> fin_cases b <;> simp [cmap_mk, cf]

/-- The star at the vertex `0`: a spanning tree of `K₄`. -/
