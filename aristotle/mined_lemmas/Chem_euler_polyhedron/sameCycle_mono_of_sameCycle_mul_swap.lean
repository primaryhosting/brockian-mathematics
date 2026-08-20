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

lemma sameCycle_mono_of_sameCycle_mul_swap {f : Perm ι} {x y a b : ι}
    (hg : (f * swap x y).SameCycle x y) (h : f.SameCycle a b) :
    (f * swap x y).SameCycle a b := by
  set g := f * swap x y with hgdef
  have hfg : g * swap x y = f := by
    rw [hgdef, mul_assoc, swap_mul_self, mul_one]
  rw [← hfg] at h
  rcases sameCycle_mul_swap_imp h with h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact h1
  · exact h1.trans (hg.trans h2)
  · exact h1.trans (hg.symm.trans h2)

/-- **Merging**: multiplying by a transposition joining two different orbits decreases the
number of orbits by one. -/
