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

lemma card_kneserVertex_one (n : ℕ) : Fintype.card (KneserVertex n 1) = n := by
  simp [Fintype.card_finset_len (α := Fin n) 1]

/-- **Lovász–Kneser theorem, base case `k = 1`.**  The chromatic number of the Kneser graph
`KG_{n,1}` — which is the complete graph on `n` vertices — is `n - 2 * 1 + 2 = n`, for `n ≥ 2`. -/
