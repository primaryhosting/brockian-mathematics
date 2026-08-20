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

lemma tree_cotree (e : (⊤ : SimpleGraph (Fin 4)).edgeSet) :
    (edgeEquiv e : Sym2 (Fin 4)) ∈ star.edgeSet ↔ (e : Sym2 (Fin 4)) ∉ star.edgeSet := by
  obtain ⟨e, he⟩ := e
  induction e using Sym2.ind with
  | _ a b =>
      rw [mem_top_edgeSet] at he
      fin_cases a <;> fin_cases b <;>
        simp_all [edgeEquiv_coe, cmap_mk, cf, SimpleGraph.mem_edgeSet, star_adj]

/-- **Euler's formula for the tetrahedron**, an instance of `Chem.euler_polyhedron`: with
`Fintype.card (Fin 4) = 4` vertices and faces and `Chem.Tetrahedron.card_top_edges` (`= 6`)
edges, this reads `4 - 6 + 4 = 2`. -/
