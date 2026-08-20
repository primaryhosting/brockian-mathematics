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

theorem euler_polyhedron {Vertex Face : Type*} [Fintype Vertex] [Fintype Face]
    {skeleton T : SimpleGraph Vertex} {dual D : SimpleGraph Face}
    [Fintype skeleton.edgeSet] [Fintype dual.edgeSet]
    [Fintype T.edgeSet] [Fintype D.edgeSet]
    (edgeEquiv : skeleton.edgeSet ≃ dual.edgeSet)
    (hT : T ≤ skeleton) (hTtree : T.IsTree)
    (hD : D ≤ dual) (hDtree : D.IsTree)
    (hcotree : ∀ e : skeleton.edgeSet,
      (edgeEquiv e : Sym2 Face) ∈ D.edgeSet ↔ (e : Sym2 Vertex) ∉ T.edgeSet) :
    Fintype.card Vertex + Fintype.card Face = Fintype.card skeleton.edgeSet + 2 := by
  classical
  -- the tree edges, counted inside the edge set of the skeleton
  have hTcard : Fintype.card {e : skeleton.edgeSet // (e : Sym2 Vertex) ∈ T.edgeSet}
      = Fintype.card T.edgeSet := Fintype.card_congr (edgeSubtypeEquiv hT)
  -- the cotree edges biject with the edges of the dual tree
  have hDcard : Fintype.card {e : skeleton.edgeSet // (e : Sym2 Vertex) ∉ T.edgeSet}
      = Fintype.card D.edgeSet := by
    refine Fintype.card_congr (Equiv.trans ?_ (edgeSubtypeEquiv hD))
    exact Equiv.subtypeEquiv (p := fun e : skeleton.edgeSet => (e : Sym2 Vertex) ∉ T.edgeSet)
      (q := fun f : dual.edgeSet => (f : Sym2 Face) ∈ D.edgeSet) edgeEquiv
      (fun e => (hcotree e).symm)
  -- splitting the skeleton edges into tree edges and cotree edges
  have hsplit : Fintype.card {e : skeleton.edgeSet // (e : Sym2 Vertex) ∈ T.edgeSet}
      + Fintype.card {e : skeleton.edgeSet // (e : Sym2 Vertex) ∉ T.edgeSet}
      = Fintype.card skeleton.edgeSet := by
    rw [← Fintype.card_sum]
    exact Fintype.card_congr (Equiv.sumCompl _)
  -- Mathlib's count of the edges of a tree
  have hTree : Fintype.card T.edgeSet + 1 = Fintype.card Vertex := by
    have := hTtree.card_edgeFinset
    rwa [SimpleGraph.edgeFinset_card] at this
  have hDTree : Fintype.card D.edgeSet + 1 = Fintype.card Face := by
    have := hDtree.card_edgeFinset
    rwa [SimpleGraph.edgeFinset_card] at this
  omega

/-- The one-point graph is a tree. -/
