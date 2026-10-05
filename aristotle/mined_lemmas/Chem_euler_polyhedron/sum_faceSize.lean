/-
/-!
# Euler Polyhedron
Category: Chemistry
Target: Chem.euler_polyhedron
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/

import Mathlib

/-!
# Euler Polyhedron
Category: Chemistry
Target: Chem.euler_polyhedron
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## Combinatorial model

We model the (boundary) surface of a convex polyhedron -- for instance a fullerene cage --
by its combinatorial incidence data together with a *tree-cotree* (interdigitating spanning
trees) decomposition of its edge set, which is the combinatorial expression of the fact that
the surface is a sphere.

Explicitly, a `PolyhedralSurface` consists of finite sets of vertices, edges and faces,
where each edge has two distinct endpoints and two distinct incident faces, and a
distinguished set `tree` of edges such that

* the edges of `tree` form a spanning tree of the vertex-edge graph (the 1-skeleton), and
* the remaining edges form a spanning tree of the dual graph on faces.

Every convex polyhedron has such a decomposition: take any spanning tree `T` of its
1-skeleton; the dual edges corresponding to the edges outside `T` then form a spanning tree
of the dual graph.

Euler's formula `V - E + F = 2` is proved from this data, and, as a chemical corollary,
that a trivalent cage all of whose faces are pentagons or hexagons has exactly 12
pentagonal faces (as in a fullerene).
-/

namespace Chem

open Finset

/-- Combinatorial data describing the surface of a convex polyhedron (e.g. a fullerene cage):
vertices, edges and faces, the two endpoints and two incident faces of each edge, and a
tree-cotree decomposition of the edge set witnessing that the surface is a sphere. -/
structure PolyhedralSurface where
  /-- The set of vertices. -/
  Vert : Type
  /-- The set of edges. -/
  Edge : Type
  /-- The set of faces. -/
  Face : Type
  [finVert : Fintype Vert]
  [finEdge : Fintype Edge]
  [finFace : Fintype Face]
  [decVert : DecidableEq Vert]
  [decEdge : DecidableEq Edge]
  [decFace : DecidableEq Face]
  /-- The (unordered) pair of endpoints of an edge. -/
  ends : Edge → Sym2 Vert
  /-- The (unordered) pair of faces incident with an edge. -/
  sides : Edge → Sym2 Face
  /-- The two endpoints of an edge are distinct. -/
  ends_not_isDiag : ∀ e, ¬ (ends e).IsDiag
  /-- The two faces incident with an edge are distinct. -/
  sides_not_isDiag : ∀ e, ¬ (sides e).IsDiag
  /-- The edges of a distinguished spanning tree of the 1-skeleton. -/
  tree : Finset Edge
  /-- The spanning tree of the 1-skeleton. -/
  primalTree : SimpleGraph Vert
  /-- The spanning tree of the dual graph. -/
  dualTree : SimpleGraph Face
  [finPrimal : Fintype primalTree.edgeSet]
  [finDual : Fintype dualTree.edgeSet]
  primalTree_isTree : primalTree.IsTree
  dualTree_isTree : dualTree.IsTree
  /-- The edges of `primalTree` are exactly the edges in `tree`. -/
  primal_edgeFinset : primalTree.edgeFinset = tree.image ends
  /-- The edges of `dualTree` are exactly the duals of the edges outside `tree`. -/
  dual_edgeFinset : dualTree.edgeFinset = treeᶜ.image sides
  /-- Distinct tree edges have distinct endpoint pairs. -/
  ends_injOn : Set.InjOn ends tree
  /-- Distinct cotree edges have distinct incident face pairs. -/
  sides_injOn : Set.InjOn sides (↑treeᶜ)

attribute [instance] PolyhedralSurface.finVert PolyhedralSurface.finEdge
  PolyhedralSurface.finFace PolyhedralSurface.decVert PolyhedralSurface.decEdge
  PolyhedralSurface.decFace PolyhedralSurface.finPrimal PolyhedralSurface.finDual

namespace PolyhedralSurface

variable (P : PolyhedralSurface)

/-- The number of vertices `V`. -/

lemma sum_faceSize : ∑ f, P.faceSize f = 2 * P.numEdges := by
  classical
  have : ∑ f : P.Face, P.faceSize f
      = ∑ e : P.Edge, (univ.filter fun f => f ∈ P.sides e).card := by
    simp only [faceSize, Finset.card_filter]
    exact Finset.sum_comm
  rw [this]
  have h2 : ∀ e : P.Edge, (univ.filter fun f => f ∈ P.sides e).card = 2 := fun e =>
    card_filter_mem_sym2 _ (P.sides_not_isDiag e)
  simp [h2, numEdges, mul_comm]

end PolyhedralSurface

/-- **Fullerenes have exactly twelve pentagonal faces.**  If every vertex of a polyhedral
surface has degree three and every face is a pentagon or a hexagon, then exactly twelve of
the faces are pentagons. -/
