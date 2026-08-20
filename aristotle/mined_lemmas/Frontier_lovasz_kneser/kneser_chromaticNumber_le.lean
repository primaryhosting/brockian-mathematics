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

theorem kneser_chromaticNumber_le (n k : ℕ) (hk : 1 ≤ k) (hn : 2 * k ≤ n) :
    (KneserGraph n k).chromaticNumber ≤ (n - 2 * k + 2 : ℕ) :=
  (kneser_colorable n k hk hn).chromaticNumber_le

/-! ### The base case `k = 1`: `KG_{n,1}` is the complete graph -/

