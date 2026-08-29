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

theorem euler_tetraCage :
    (tetraCage.V.card : ℤ) - (tetraCage.E.card : ℤ) + (tetraCage.F.card : ℤ) = 2 :=
  euler_cage ConstructibleCage.tetra

end Chem

import Mathlib
import RequestProject.ChemIncidence

/-!
# The buckminsterfullerene cage C₆₀ with explicit incidence data

The truncated icosahedron — the carbon skeleton of buckminsterfullerene C₆₀ — is written down
here as a concrete `Chem.Cage`: 60 carbon atoms (vertices `0,…,59`), 90 bonds (edges
`0,…,89`) and 32 rings (faces `0,…,31`), with the endpoints of every bond and the bonds
bounding every ring given explicitly.  The vertices are the 60 "darts" of the icosahedron
(a vertex together with an incident edge), the rings are the 12 pentagons obtained by cutting
off the icosahedron's vertices and the 20 hexagons coming from its triangles.

All the chemically relevant facts about this structure are then checked by decision procedure:
it is a well-formed closed surface (every bond lies on exactly two rings), every atom has
exactly three bonds, there are exactly 12 pentagonal and 20 hexagonal rings, and Euler's
formula `60 - 90 + 32 = 2` holds.
-/

namespace Chem

set_option maxRecDepth 100000

/-- The carbon skeleton of C₆₀ (the truncated icosahedron) as a cage with explicit incidence
data: 60 vertices, 90 edges, 32 faces. -/
