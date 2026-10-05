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

noncomputable def tetTreeEquivCotree :
    {e // tetIsTreeEdge e} ≃ {e // ¬ tetIsTreeEdge e} := Fintype.equivOfCardEq (by decide)

/-- Identification of the edges of the tetrahedron with the edges of its dual (again a
tetrahedron), chosen so that the tree edges correspond to the non-tree edges. -/
