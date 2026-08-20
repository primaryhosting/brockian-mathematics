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

lemma bot_isTree_fin_one : (⊥ : SimpleGraph (Fin 1)).IsTree := by
  constructor
  · exact ⟨fun a b => (Subsingleton.elim a b) ▸ SimpleGraph.Reachable.refl a⟩
  · intro a p hp
    cases p with
    | nil => exact hp.ne_nil rfl
    | cons h _ => exact h.elim

/-- The hypotheses of `Chem.euler_polyhedron` are satisfiable: the degenerate polyhedron
with a single vertex, no edge and a single face. (A sanity check that the statement is not
vacuous.) -/
example : Fintype.card (Fin 1) + Fintype.card (Fin 1)
    = Fintype.card (⊥ : SimpleGraph (Fin 1)).edgeSet + 2 :=
  euler_polyhedron (Equiv.refl _) le_rfl bot_isTree_fin_one le_rfl bot_isTree_fin_one
    (fun e => absurd e.2 (by simp))

/-! ### A concrete polyhedron: the tetrahedron

We check that the hypotheses of `Chem.euler_polyhedron` really are met by an honest convex
polyhedron. For the tetrahedron the 1-skeleton is the complete graph `K₄` on `Fin 4`, and,
labelling each face by the vertex it misses, the dual graph is again `K₄`: two faces share
an edge exactly when the two vertices labelling them are distinct. Under this labelling the
edge `{a,b}` of the tetrahedron separates the two faces labelled by the *complementary*
pair, so the incidence bijection is the complementation involution `Chem.Tetrahedron.cmap`
on pairs. The star at the vertex `0` is a spanning tree of `K₄`, and the complementary
edges `{1,2}, {1,3}, {2,3}` correspond to the dual edges `{0,3}, {0,2}, {0,1}`, i.e. to the
star at `0` in the dual: a tree–cotree decomposition. Euler's formula then gives
`4 - 6 + 4 = 2`. -/
namespace Tetrahedron

/-- Complementation on pairs of vertices of the tetrahedron: `{a,b} ↦ {c,d}` where `{c,d}`
is the complementary pair (and `{a,a} ↦ {a,a}`). -/
