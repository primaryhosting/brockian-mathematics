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

theorem exists_sphericalMap_triangle :
    ∃ s a : Perm (Fin 6), IsSphericalMap Finset.univ s a := by
  refine ⟨(1 * swap 1 2) * swap 0 4 * swap 3 5, (swap 0 1 * swap 2 3) * swap 4 5, ?_⟩
  have hbase : IsSphericalMap ({0, 1} : Finset (Fin 6)) 1 (swap 0 1) :=
    IsSphericalMap.base (by decide)
  have hpath : IsSphericalMap (insert 2 (insert 3 ({0, 1} : Finset (Fin 6))))
      (1 * swap 1 2) (swap 0 1 * swap 2 3) :=
    hbase.pendant (d := 1) (x := 2) (y := 3) (by decide) (by decide) (by decide) (by decide)
  have htri := hpath.chord (d := 0) (e := 3) (x := 4) (y := 5) (by decide) (by decide)
    (by decide) ⟨2, by decide⟩ (by decide) (by decide) (by decide)
  have hset : insert (4 : Fin 6) (insert 5 (insert 2 (insert 3 ({0, 1} : Finset (Fin 6)))))
      = Finset.univ := by decide
  rwa [hset] at htri

/-- Euler's formula for the triangle map. -/
