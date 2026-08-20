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

theorem lovasz_kneser_k_one (n : ℕ) (hn : 2 ≤ n) :
    (KneserGraph n 1).chromaticNumber = (n - 2 * 1 + 2 : ℕ) := by
  have htop : (KneserGraph n 1).chromaticNumber = (Fintype.card (KneserVertex n 1) : ℕ∞) := by
    rw [kneserGraph_one_eq_top]
    exact SimpleGraph.chromaticNumber_top
  rw [htop, card_kneserVertex_one n]
  congr 1
  omega

/-! ### The base case `n = 2k`: `KG_{2k,k}` is a perfect matching -/

/-- **Lovász–Kneser theorem, base case `n = 2k`.**  The chromatic number of `KG_{2k,k}` is
`2k - 2k + 2 = 2`, for `k ≥ 1`. -/
