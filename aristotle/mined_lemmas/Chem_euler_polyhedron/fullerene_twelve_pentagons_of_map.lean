import Mathlib

/-!
# Counting the orbits of a permutation, and how a transposition changes the count

This file develops the basic combinatorial tool behind Euler's polyhedron formula:
for a permutation `f` of a finite type, multiplying by a transposition `swap x y`
either *merges* two orbits (if `x` and `y` lie in different orbits of `f`) or
*splits* one orbit into two (if `x` and `y` lie in the same orbit of `f`).
-/

open Equiv Equiv.Perm Function

namespace Polyhedron

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The number of orbits (cycles, including fixed points) of a permutation of a finite type. -/

theorem fullerene_twelve_pentagons_of_map {s a : Perm ι} {P Hex : ℕ}
    (H : IsSphericalMap (Finset.univ : Finset ι) s a)
    (hdeg : 3 * numVertices s = 2 * numEdges a)
    (hfaces : numFaces s a = P + Hex)
    (hedges : 2 * numEdges a = 5 * P + 6 * Hex) : P = 12 :=
  fullerene_twelve_pentagons hdeg hfaces hedges (euler_polyhedron_nat H)

end Chem

import RequestProject.SphericalMap

/-!
# A concrete spherical map

To show that the notion `Polyhedron.IsSphericalMap` is not vacuous we build an explicit
example: a triangle drawn on the sphere, with `3` vertices, `3` edges and `2` faces
(the inside and the outside of the triangle), realised on the six darts `Fin 6`.
-/

open Equiv Equiv.Perm Polyhedron

namespace Chem

/-- A triangle drawn on the sphere, on the six darts `Fin 6`: three vertices, three edges and
two faces.  In particular `Chem.euler_polyhedron` applies to a genuine map. -/
