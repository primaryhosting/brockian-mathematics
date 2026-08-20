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

lemma exists_eq_pair_of_mem {s : Finset ι} (hs : s.card = 2) {x : ι} (hx : x ∈ s) :
    ∃ y, y ≠ x ∧ s = {x, y} := by
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hs
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · exact ⟨b, fun h => hab h.symm, rfl⟩
  · exact ⟨a, hab, Finset.pair_comm _ _⟩

/-- An intersecting family of `2`-element sets in which no element of a member is common to
all members has at most three members (it is a triangle). -/
