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

namespace Chem

/-- **Fullerene / trivalent polyhedron count of pentagons.**

A convex (equivalently, planar, connected) polyhedron with `V` vertices, `E` edges and
`F` faces satisfies Euler's formula `V - E + F = 2`.  Assume moreover that it is
*trivalent*: every vertex lies on exactly three edges, so summing vertex degrees gives
`3 * V = 2 * E`; and that every face is a pentagon or a hexagon, say `p` pentagons and
`h` hexagons, so `F = p + h` and summing face degrees gives `5 * p + 6 * h = 2 * E`.

Then there are exactly `12` pentagons, whatever the number of hexagons. -/

theorem fullerene_pentagons_count
    (V E F p h : ℕ)
    (hEuler : (V : ℤ) - E + F = 2)
    (htrivalent : 3 * V = 2 * E)
    (hfaces : F = p + h)
    (hdeg : 5 * p + 6 * h = 2 * E) :
    p = 12 := by
  omega

/-- **Fullerene / trivalent polyhedron: exactly 12 pentagonal faces.**

Here the faces are indexed by a finite type `Face`, and `size f` is the number of edges
(equivalently vertices) of the face `f`.  The hypotheses are:

* `hsize`: every face is a pentagon or a hexagon;
* `hEuler`: Euler's formula `V - E + F = 2` for the polyhedron, `F` being the number of faces;
* `htrivalent`: every vertex meets exactly three edges (`3 * V = 2 * E`);
* `hdeg`: each edge lies on exactly two faces, i.e. the face sizes sum to `2 * E`.

Conclusion: exactly `12` faces are pentagons. -/
