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

def edgeSubtypeEquiv (h : H ≤ G) :
    {e : G.edgeSet // (e : Sym2 α) ∈ H.edgeSet} ≃ H.edgeSet where
  toFun e := ⟨(e.1 : Sym2 α), e.2⟩
  invFun e := ⟨⟨(e : Sym2 α), edgeSet_mono h e.2⟩, e.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

end TreeCotree

/-- **Euler's polyhedron formula**, `V - E + F = 2`, in the form `V + F = E + 2`.

The combinatorial data of (the surface of) a convex polyhedron — say a fullerene cage — is:

* a finite vertex set `Vertex` and the `skeleton` graph on it (the 1-skeleton of the
  polyhedron, whose edges are the edges of the polyhedron);
* a finite face set `Face` and the `dual` graph on it (two faces are adjacent when they
  share an edge);
* the incidence bijection `edgeEquiv` matching every edge of the polyhedron with the dual
  edge joining the two faces it separates.

The input coming from convexity (equivalently: from the surface being a sphere) is the
classical *tree–cotree decomposition*: the edge set of a polyhedron splits into a spanning
tree `T` of the skeleton and, on the complementary edges, a spanning tree `D` of the dual
graph. Given that decomposition, Euler's formula is a counting identity, obtained from
Mathlib's `SimpleGraph.IsTree.card_edgeFinset` (`|E(T)| + 1 = |V|` for a tree `T`) applied
to `T` and to `D`. -/
