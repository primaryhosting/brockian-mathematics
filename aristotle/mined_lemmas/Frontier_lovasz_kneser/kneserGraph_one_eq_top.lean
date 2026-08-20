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

lemma kneserGraph_one_eq_top (n : ℕ) : KneserGraph n 1 = ⊤ := by
  ext a b
  simp only [kneserGraph_adj, SimpleGraph.top_adj]
  refine ⟨fun h => h.1, fun hab => ⟨hab, ?_⟩⟩
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp a.2
  obtain ⟨y, hy⟩ := Finset.card_eq_one.mp b.2
  have hxy : x ≠ y := by
    rintro rfl
    exact hab (Subtype.ext (hx.trans hy.symm))
  simp [hx, hy, hxy]

