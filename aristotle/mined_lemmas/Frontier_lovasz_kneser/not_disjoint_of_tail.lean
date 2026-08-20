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

lemma not_disjoint_of_tail {n k : ℕ} (c : Fin n) (hc : (c : ℕ) = n - 2 * k + 1)
    (a b : Finset (Fin n)) (ha : a.card = k) (hb : b.card = k)
    (ha' : a ⊆ Finset.Ici c) (hb' : b ⊆ Finset.Ici c) :
    ¬ Disjoint a b := by
  intro hd
  have h1 : (a ∪ b).card = 2 * k := by
    rw [Finset.card_union_of_disjoint hd, ha, hb]; ring
  have h3 := Finset.card_le_card (Finset.union_subset ha' hb')
  rw [Fin.card_Ici, hc, h1] at h3
  have : (c : ℕ) < n := c.isLt
  omega

/-- The Kneser graph `KG_{n,k}` is colorable with `n - 2k + 2` colors, for `1 ≤ k` and
`2k ≤ n`.  (This is the easy half of Lovász's theorem.) -/
