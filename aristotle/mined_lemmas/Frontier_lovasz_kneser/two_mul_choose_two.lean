import Mathlib

/-!
# Covering the pairs of a finite set by intersecting families

This file contains the combinatorial core of the case `k = 2` of the Lovász–Kneser theorem.

A proper colouring of the Kneser graph `KG_{n,2}` is exactly a partition of the `2`-element
subsets of an `n`-element set into *intersecting families*.  Such a family is either contained
in a "star" (all its members share a common element) or is a "triangle" (and then has exactly
three members).  This dichotomy drives an induction showing that at least `n - 2` families are
needed.
-/

namespace Frontier

open Finset

variable {ι : Type*} [DecidableEq ι]

/-- A two-element finset containing `x` is `{x, y}` for some `y ≠ x`. -/

lemma two_mul_choose_two (m : ℕ) : 2 * m.choose 2 = m * (m - 1) := by
  induction m with
  | zero => simp
  | succ p ih =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right, Nat.mul_add, ih]
    cases p with
    | zero => simp
    | succ q => simp only [Nat.succ_sub_one]; ring

/-- **Key counting lemma.**  If the `2`-element subsets of a finite set `V` are coloured so
that disjoint pairs receive different colours, then at least `#V - 2` colours occur. -/
