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

theorem tetrahedron_counts :
    tetrahedron.numVertices = 4 ∧ tetrahedron.numEdges = 6 ∧ tetrahedron.numFaces = 4 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [PolyhedralSurface.numVertices, PolyhedralSurface.numEdges,
      PolyhedralSurface.numFaces, tetrahedron, Nat.card_eq_fintype_card] <;>
    decide

/-!
## A chemical consequence: every fullerene cage has exactly twelve pentagons
-/

/-- **Fullerene pentagon count.** A fullerene cage is a convex polyhedron whose faces are
pentagons (`p` of them) and hexagons (`h` of them) and in which every vertex has degree three.
Euler's formula forces `p = 12`, independently of the number of hexagons.

The hypotheses are the numerical consequences of the chemical description: `3 * V = 2 * E`
(each vertex lies on three edges, each edge has two ends), `F = p + h`, and `5 * p + 6 * h = 2 * E`
(each edge borders exactly two faces). -/
