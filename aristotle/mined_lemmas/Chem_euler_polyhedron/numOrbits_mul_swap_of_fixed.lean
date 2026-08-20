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

lemma numOrbits_mul_swap_of_fixed {f : Perm ι} {d x : ι} (hx : f x = x) (hdx : d ≠ x) :
    numOrbits (f * swap d x) + 1 = numOrbits f :=
  numOrbits_mul_swap_of_not_sameCycle (fun h => hdx (h.eq_of_right hx))

omit [DecidableEq ι] in
/-- The identity permutation has one orbit per point. -/
