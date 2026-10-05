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

theorem euler_bipyramid :
    ((insert 4 {0, 1, 2, 3} : Finset ℕ).card : ℤ) - (({6, 7, 8} ∪ {0, 1, 2, 3, 4, 5} :
      Finset ℕ).card : ℤ) + (({4, 5} ∪ {0, 1, 2, 3} : Finset ℕ).card : ℤ) = 2 :=
  euler_surface constructibleSurface_bipyramid

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

import Mathlib
import RequestProject.Chem

/-!
# Fullerene cages: consequences of Euler's polyhedron formula

Chemical consequences of `Chem.euler_polyhedron` for closed carbon cages.  A fullerene cage is
a convex polyhedron in which every carbon atom has three neighbours (the polyhedron is
3-regular) and every ring is a pentagon or a hexagon.  Euler's formula pins down the whole
count table of such a cage: there are always exactly 12 pentagons, and with `h` hexagons the
cage has `20 + 2h` atoms, `30 + 3h` bonds and `12 + h` rings.
-/

namespace Chem

/-- Full count table of a fullerene cage with `h` hexagonal rings: 12 pentagons,
`F = 12 + h` faces, `V = 20 + 2h` atoms and `E = 30 + 3h` bonds. -/
