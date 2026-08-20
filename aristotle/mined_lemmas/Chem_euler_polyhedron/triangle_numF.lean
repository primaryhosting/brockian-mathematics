import RequestProject.EulerPolyhedron

/-!
# Fullerene cages have exactly twelve pentagonal faces

A fullerene cage is a polyhedral (spherical) carbon cage in which every atom has exactly three
neighbours and every ring is a pentagon or a hexagon.  Combining Euler's formula
`V - E + F = 2` with the two incidence counts `3V = 2E` and `5p + 6h = 2E` forces the number
of pentagons to be exactly `12`, no matter how many hexagons there are.
-/

namespace Chem

open Equiv Equiv.Perm Finset

variable {α : Type*} [DecidableEq α] [Fintype α]

/-! ### The edge involution -/

omit [Fintype α] in
/-- The edge permutation of a sphere map is an involution. -/

theorem triangle_numF :
    numF ({0, 1, 2, 3, 4, 5} : Finset (Fin 6)) (swap 1 4 * (swap 3 5 * swap 0 2))
      (swap 4 5 * (swap 2 3 * swap 0 1)) = 2 := by
  decide

/-- Euler's formula, checked on the triangle: `3 - 3 + 2 = 2`. -/
example :
    numV ({0, 1, 2, 3, 4, 5} : Finset (Fin 6)) (swap 1 4 * (swap 3 5 * swap 0 2))
      + numF ({0, 1, 2, 3, 4, 5} : Finset (Fin 6)) (swap 1 4 * (swap 3 5 * swap 0 2))
        (swap 4 5 * (swap 2 3 * swap 0 1))
      = numE ({0, 1, 2, 3, 4, 5} : Finset (Fin 6)) (swap 4 5 * (swap 2 3 * swap 0 1)) + 2 :=
  euler_polyhedron triangle_isSphereMap

end Chem

import RequestProject.PermOrbits

/-!
# Euler's polyhedron formula `V - E + F = 2`

The surface of a convex polyhedron (a fullerene cage, say) is described combinatorially by a
*map on the sphere*.  We use the classical dart (half-edge) model of a map:

* a finite set `D` of **darts** (each edge of the polyhedron contributes two darts,
  one for each of its two ends);
* a permutation `s` (the *rotation*), whose cycles are the **vertices**: `s` rotates a dart
  to the next dart around the same vertex, in the cyclic order induced by the surface;
* a fixed-point-free involution `e`, whose cycles are the **edges**: `e` exchanges the two
  darts of an edge.

The **faces** are then the cycles of `s * e`.  Thus

* `V = norb s D`, `E = norb e D`, `F = norb (s * e) D`.

Being drawn on a *sphere* (as opposed to some surface of higher genus) is the combinatorial
content of Euler's formula, and it has to enter the statement.  We encode it, as is standard,
by the inductive generation of spherical maps: starting from the map consisting of a single
edge, every polyhedral surface is obtained by repeatedly

* attaching a new edge with a new endpoint of degree one at some corner (`pendant`), or
* drawing a new edge inside an existing face, joining two corners of that face (`chord`).

Both moves are drawings on the sphere, and every map drawn on the sphere arises this way.
The main theorem `Chem.euler_polyhedron` states that any such map satisfies

`V + F = E + 2`,  i.e.  `V - E + F = 2`.
-/

namespace Chem

open Equiv Equiv.Perm Finset

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- A map drawn on the sphere, in the dart model: `D` is the set of darts, `s` the rotation
(its cycles are the vertices) and `e` the edge involution (its cycles are the edges).

The three constructors are: a single edge; attaching a pendant edge (a new vertex of degree
one) at the corner following the dart `x`; and drawing a chord inside a face, joining the
corner following `x` to the corner following `y`, both corners lying on a common face.
In the last two cases `c` and `d` are the two new darts of the new edge. -/
inductive IsSphereMap : Finset α → Perm α → Perm α → Prop
  | edge {a b : α} (hab : a ≠ b) : IsSphereMap {a, b} 1 (swap a b)
  | pendant {D : Finset α} {s e : Perm α} (h : IsSphereMap D s e) {x c d : α} (hx : x ∈ D)
      (hc : c ∉ D) (hd : d ∉ insert c D) :
      IsSphereMap (insert c (insert d D)) (swap (s x) c * s) (swap c d * e)
  | chord {D : Finset α} {s e : Perm α} (h : IsSphereMap D s e) {x y c d : α} (hx : x ∈ D)
      (hy : y ∈ D) (hxy : x ≠ y) (hface : (s * e).SameCycle (s x) (s y))
      (hc : c ∉ D) (hd : d ∉ insert c D) :
      IsSphereMap (insert c (insert d D)) (swap (s x) c * (swap (s y) d * s)) (swap c d * e)

/-- The number of vertices of a map: the number of cycles of the rotation. -/
