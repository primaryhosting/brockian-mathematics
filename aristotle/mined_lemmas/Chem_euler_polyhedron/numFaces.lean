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

noncomputable def numFaces (s a : Perm ι) : ℕ := numOrbits (a * s)

/-- **Euler's polyhedron formula**.  For a convex polyhedron -- for instance a fullerene cage --
the boundary complex is a combinatorial map of the sphere, and for any such map
`V - E + F = 2`. -/
