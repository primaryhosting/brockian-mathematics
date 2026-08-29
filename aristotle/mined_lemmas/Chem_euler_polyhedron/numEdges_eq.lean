import Mathlib

/-!
# Euler Polyhedron
Category: Chemistry
Target: Chem.euler_polyhedron
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open SimpleGraph

/-- A combinatorial model of the surface of a convex polyhedron (e.g. a fullerene cage).

The data consist of the vertex set, the face set, the *skeleton* (the 1-skeleton graph of the
polyhedron, a simple graph since a convex polyhedron has no multiple edges), the *dual* graph on
the faces (also simple, since two facets of a convex polytope meet in at most one edge), and the
bijection `dualEdge` between the edges of the skeleton and the edges of the dual, coming from the
fact that every edge of a polyhedron is shared by exactly two faces.

Sphericity (planarity) of the surface is encoded by the classical *tree–cotree* structure: there
is a spanning tree `tree` of the skeleton whose complementary edges are exactly the edges of a
spanning tree `cotree` of the dual graph. Such an interdigitating pair of trees exists precisely
for maps on the sphere, and in particular for every convex polyhedron. -/
structure PolyhedralSurface where
  /-- The vertices of the polyhedron. -/
  Vertex : Type
  /-- The faces of the polyhedron. -/
  Face : Type
  [finiteVertex : Finite Vertex]
  [finiteFace : Finite Face]
  /-- The 1-skeleton: vertices and edges of the polyhedron. -/
  skeleton : SimpleGraph Vertex
  /-- The dual graph: faces are adjacent when they share an edge. -/
  dual : SimpleGraph Face
  /-- Each edge of the polyhedron is shared by exactly two faces; this is the resulting
  bijection between primal and dual edges. -/
  dualEdge : skeleton.edgeSet ≃ dual.edgeSet
  /-- A spanning tree of the skeleton. -/
  tree : SimpleGraph Vertex
  tree_le : tree ≤ skeleton
  tree_isTree : tree.IsTree
  /-- A spanning tree of the dual graph. -/
  cotree : SimpleGraph Face
  cotree_le : cotree ≤ dual
  cotree_isTree : cotree.IsTree
  /-- The two trees interdigitate: the dual edges of the non-tree edges are exactly the
  cotree edges. -/
  interdigitating : ∀ e : skeleton.edgeSet,
    (dualEdge e : Sym2 Face) ∈ cotree.edgeSet ↔ (e : Sym2 Vertex) ∉ tree.edgeSet

namespace PolyhedralSurface

instance (P : PolyhedralSurface) : Finite P.Vertex := P.finiteVertex
instance (P : PolyhedralSurface) : Finite P.Face := P.finiteFace

/-- The number of vertices. -/

theorem numEdges_eq (P : PolyhedralSurface) :
    P.numEdges = Nat.card P.tree.edgeSet + Nat.card P.cotree.edgeSet := by
  classical
  set p : P.skeleton.edgeSet → Prop := fun e => (e : Sym2 P.Vertex) ∈ P.tree.edgeSet with hp
  have e1 : {e : P.skeleton.edgeSet // p e} ≃ P.tree.edgeSet :=
    Equiv.subtypeSubtypeEquivSubtype (fun {x} hx => edgeSet_mono P.tree_le hx)
  have e2 : {e : P.skeleton.edgeSet // ¬ p e} ≃
      {d : P.dual.edgeSet // (d : Sym2 P.Face) ∈ P.cotree.edgeSet} :=
    Equiv.subtypeEquiv P.dualEdge (fun e => (P.interdigitating e).symm)
  have e3 : {d : P.dual.edgeSet // (d : Sym2 P.Face) ∈ P.cotree.edgeSet} ≃ P.cotree.edgeSet :=
    Equiv.subtypeSubtypeEquivSubtype (fun {x} hx => edgeSet_mono P.cotree_le hx)
  have hsplit : Nat.card P.skeleton.edgeSet
      = Nat.card {e : P.skeleton.edgeSet // p e} + Nat.card {e : P.skeleton.edgeSet // ¬ p e} := by
    rw [← Nat.card_sum]
    exact Nat.card_congr (Equiv.sumCompl p).symm
  rw [numEdges, hsplit, Nat.card_congr e1, Nat.card_congr (e2.trans e3)]

end PolyhedralSurface

/-- **Euler's polyhedron formula**: for a convex polyhedron (for instance a fullerene cage),
`V - E + F = 2`.

The polyhedron is modelled combinatorially by `Chem.PolyhedralSurface`; sphericity is encoded by
the interdigitating pair of spanning trees of the skeleton and of the dual graph. The proof is the
tree–cotree argument: the spanning tree has `V - 1` edges and the dual spanning tree has `F - 1`
edges (`SimpleGraph.isTree_iff_connected_and_card`), and every edge is counted exactly once. -/
