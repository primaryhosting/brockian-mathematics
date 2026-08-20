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

theorem lovasz_kneser_two_k (k : ℕ) (hk : 1 ≤ k) :
    (KneserGraph (2 * k) k).chromaticNumber = (2 * k - 2 * k + 2 : ℕ) := by
  classical
  have hle : (KneserGraph (2 * k) k).chromaticNumber ≤ (2 * k - 2 * k + 2 : ℕ) :=
    kneser_chromaticNumber_le (2 * k) k hk le_rfl
  refine le_antisymm hle ?_
  have hklt : k < 2 * k := by omega
  set c : Fin (2 * k) := ⟨k, hklt⟩ with hcdef
  set A : Finset (Fin (2 * k)) := Finset.Iio c with hA
  set B : Finset (Fin (2 * k)) := Finset.Ici c with hB
  have hAcard : A.card = k := by rw [hA, Fin.card_Iio]
  have hBcard : B.card = k := by rw [hB, Fin.card_Ici]; simp [hcdef]; omega
  have hdisjAB : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro i hi hi'
    rw [hA, Finset.mem_Iio] at hi
    rw [hB, Finset.mem_Ici] at hi'
    exact absurd hi (not_lt.mpr hi')
  let va : KneserVertex (2 * k) k := ⟨A, hAcard⟩
  let vb : KneserVertex (2 * k) k := ⟨B, hBcard⟩
  have hne : va ≠ vb := by
    intro h
    have hAB : A = B := congrArg Subtype.val h
    have hcB : c ∈ B := Finset.mem_Ici.mpr le_rfl
    rw [← hAB, hA, Finset.mem_Iio] at hcB
    exact lt_irrefl c hcB
  have hge : (2 : ℕ∞) ≤ (KneserGraph (2 * k) k).chromaticNumber := by
    refine SimpleGraph.le_chromaticNumber_of_pairwise_adj (ι := Fin 2) (n := 2)
      (f := fun i => if i = 0 then va else vb) ?_ ?_
    · simp
    · intro i j hij
      have hadj : (KneserGraph (2 * k) k).Adj va vb := ⟨hne, hdisjAB⟩
      fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · simpa using hadj
      · simpa using hadj.symm
      · exact absurd rfl hij
  simpa using hge

/-! ### The case `k = 2` -/

/-- **Lovász–Kneser theorem, the case `k = 2`.**  The chromatic number of `KG_{n,2}` is
`n - 2 * 2 + 2 = n - 2`, for `n ≥ 4`.  The lower bound is proved combinatorially, via the
fact that an intersecting family of pairs is either a star or a triangle. -/
