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

lemma card_subtype_ne_add_one {β : Type*} [Finite β] (b : β) :
    Nat.card {q : β // q ≠ b} + 1 = Nat.card β := by
  classical
  have h := Nat.card_congr (Equiv.optionSubtypeNe b)
  rw [Finite.card_option] at h
  exact h

omit [Fintype ι] in
/-- Every `SameCycle` relation for `f * swap x y` is contained in the "merged" relation
built from `f`. -/
