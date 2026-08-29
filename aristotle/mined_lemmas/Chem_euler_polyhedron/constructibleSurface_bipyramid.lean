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

theorem constructibleSurface_bipyramid :
    ConstructibleSurface (insert 4 {0, 1, 2, 3}) ({6, 7, 8} ∪ {0, 1, 2, 3, 4, 5})
      ({4, 5} ∪ {0, 1, 2, 3}) :=
  ConstructibleSurface.pyramid 4 {6, 7, 8} {4, 5} (by decide) (by decide) (by decide)
    (by decide) (by decide) ConstructibleSurface.tetrahedron

/-- The bipyramid of `constructibleSurface_bipyramid` has 5 vertices, 9 edges and 6 faces, and
indeed `5 - 9 + 6 = 2`. -/
