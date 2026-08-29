import Mathlib
import RequestProject.Chem

/-!
# Polyhedral cages with full incidence data

The previous modules describe a polyhedral surface by its vertex, edge and face sets.  Here the
incidence structure itself is formalized: a `Cage` carries, besides the three finite sets, the
endpoint set of every edge and the boundary-edge set of every face.  Well-formedness (`Cage.WF`)
demands what a closed polyhedral surface must satisfy:

* every edge has exactly two endpoints, both of them vertices;
* every face is bounded by at least three edges of the surface;
* **every edge lies on exactly two faces** — the closed-surface condition.

The two basic construction steps (subdividing an edge, splitting a face by a diagonal) are
defined on the incidence data and are proved to preserve well-formedness, and Euler's formula
`|V| - |E| + |F| = 2` is proved for every cage built in this way.
-/

namespace Chem

open Finset

/-- A polyhedral cage: finite sets of vertices, edges and faces together with the incidence
data (endpoints of each edge, boundary edges of each face). -/
structure Cage where
  /-- The vertex set. -/
  V : Finset ℕ
  /-- The edge set. -/
  E : Finset ℕ
  /-- The face set. -/
  F : Finset ℕ
  /-- The two endpoints of an edge. -/
  ends : ℕ → Finset ℕ
  /-- The boundary edges of a face. -/
  sides : ℕ → Finset ℕ

/-- Well-formedness of a cage: edges have two endpoints among the vertices, faces are bounded
by at least three edges of the cage, and every edge lies on exactly two faces. -/

theorem isPolyhedron_octahedron : IsPolyhedron 6 12 8 :=
  isPolyhedron_iterate_split 4 (isPolyhedron_iterate_subdivide 2 IsPolyhedron.tetrahedron)

/-- The dodecahedron: 20 vertices, 30 edges, 12 faces.  This is also the smallest fullerene
cage, C₂₀. -/
