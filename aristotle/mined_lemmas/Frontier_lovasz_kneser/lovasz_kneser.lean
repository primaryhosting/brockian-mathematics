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

theorem lovasz_kneser (n k : ℕ) (hk : 1 ≤ k) (hn : 2 * k ≤ n)
    (hcase : k = 1 ∨ k = 2 ∨ n = 2 * k) :
    (KneserGraph n k).chromaticNumber = (n - 2 * k + 2 : ℕ) := by
  rcases hcase with rfl | rfl | rfl
  · exact lovasz_kneser_k_one n (by omega)
  · exact lovasz_kneser_k_two n (by omega)
  · exact lovasz_kneser_two_k k hk

end Frontier

