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

def tetrahedron : PolyhedralSurface where
  Vert := Fin 4
  Edge := Fin 6
  Face := Fin 4
  ends := ![s(0, 1), s(0, 2), s(0, 3), s(1, 2), s(1, 3), s(2, 3)]
  sides := ![s(2, 3), s(1, 3), s(1, 2), s(0, 3), s(0, 2), s(0, 1)]
  ends_not_isDiag := by decide
  sides_not_isDiag := by decide
  tree := {0, 1, 2}
  primalTree := SimpleGraph.fromRel (fun a b : Fin 4 => a = 0 ∧ b ≠ 0)
  dualTree := SimpleGraph.fromRel (fun a b : Fin 4 => a = 0 ∧ b ≠ 0)
  primalTree_isTree := star4_isTree
  dualTree_isTree := star4_isTree
  primal_edgeFinset := by decide
  dual_edgeFinset := by decide
  ends_injOn := by decide
  sides_injOn := by decide

example : tetrahedron.numVertices = 4 := by decide
example : tetrahedron.numEdges = 6 := by decide
example : tetrahedron.numFaces = 4 := by decide

end Chem

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

