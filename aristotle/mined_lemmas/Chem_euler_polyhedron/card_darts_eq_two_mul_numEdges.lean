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

theorem card_darts_eq_two_mul_numEdges {s a : Perm ι}
    (H : IsSphericalMap (Finset.univ : Finset ι) s a) :
    Fintype.card ι = 2 * numEdges a := by
  have h := H.card_darts
  rw [Finset.card_univ] at h
  simp only [numEdges]
  omega

/-- Euler's formula in natural-number form: `V + F = E + 2`. -/
