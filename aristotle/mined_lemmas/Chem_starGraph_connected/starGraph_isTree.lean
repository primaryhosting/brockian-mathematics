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

/-! ### Star graphs are trees

We need a supply of concrete finite trees in order to exhibit examples of the
structure defined below; the simplest such family is the star graph. -/

/-- The star graph on `V` centred at `c`: `a` and `b` are adjacent iff they are
distinct and one of them is the centre `c`. -/

lemma starGraph_isTree {V : Type*} [Finite V] [Nonempty V] (c : V) : (starGraph c).IsTree := by
  rw [SimpleGraph.isTree_iff_connected_and_card]
  exact ⟨starGraph_connected c, starGraph_card_edgeSet c⟩

/-! ### Polyhedral surfaces

A convex polyhedron (a fullerene cage, say) determines a map on the sphere: its
vertices, edges and faces.  The combinatorial content of *sphericity* that
Euler's formula needs is the classical **tree–cotree decomposition**: the edge
set of a map drawn on the sphere splits into a spanning tree of the graph of the
polyhedron together with a spanning tree of the dual graph (whose vertices are
the faces of the polyhedron).  Indeed, given a spanning tree `T` of the
vertex–edge graph, the edges *not* in `T` are exactly the edges of a spanning
tree of the dual graph.

We take this decomposition as the data attached to a convex polyhedron. -/

/-- Combinatorial data of a convex polyhedron (a map on the sphere), recorded
through its tree–cotree decomposition: a spanning tree of the polyhedron's graph
on its vertices, a spanning tree of the dual graph on its faces, and the fact
that these two trees use each edge exactly once between them. -/
structure PolyhedralSurface where
  /-- The vertices of the polyhedron. -/
  Vertex : Type
  /-- The edges of the polyhedron. -/
  Edge : Type
  /-- The faces of the polyhedron. -/
  Face : Type
  [finiteVertex : Finite Vertex]
  [finiteEdge : Finite Edge]
  [finiteFace : Finite Face]
  /-- A spanning tree of the graph of the polyhedron. -/
  primalTree : SimpleGraph Vertex
  /-- A spanning tree of the dual graph, on the set of faces. -/
  dualTree : SimpleGraph Face
  /-- `primalTree` is indeed a tree (and spans, since it is a graph on all
  vertices). -/
  primalTree_isTree : primalTree.IsTree
  /-- `dualTree` is indeed a tree (and spans all faces). -/
  dualTree_isTree : dualTree.IsTree
  /-- Tree–cotree decomposition: every edge of the polyhedron belongs either to
  the spanning tree or to the dual spanning tree, and to exactly one of them. -/
  edge_partition : Nat.card Edge = Nat.card primalTree.edgeSet + Nat.card dualTree.edgeSet

attribute [instance] PolyhedralSurface.finiteVertex PolyhedralSurface.finiteEdge
  PolyhedralSurface.finiteFace

namespace PolyhedralSurface

variable (P : PolyhedralSurface)

/-- The number of vertices `V`. -/
