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

lemma numOrbits_mul_swap_of_sameCycle {f : Perm ι} {x y : ι} (hxy : x ≠ y)
    (h : f.SameCycle x y) : numOrbits (f * swap x y) = numOrbits f + 1 := by
  have hnot : ¬ (f * swap x y).SameCycle x y := not_sameCycle_mul_swap hxy h
  have hmerge := numOrbits_mul_swap_of_not_sameCycle (f := f * swap x y) hnot
  rw [mul_assoc, swap_mul_self, mul_one] at hmerge
  exact hmerge.symm

/-- Inserting a fixed point `x` into the orbit of `d` (i.e. `d ↦ x ↦ f d`) merges the
singleton orbit `{x}` with the orbit of `d`. -/
