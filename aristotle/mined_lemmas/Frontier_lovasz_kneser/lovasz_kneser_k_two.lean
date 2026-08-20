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

theorem lovasz_kneser_k_two (n : ℕ) (hn : 4 ≤ n) :
    (KneserGraph n 2).chromaticNumber = (n - 2 * 2 + 2 : ℕ) := by
  classical
  refine le_antisymm (kneser_chromaticNumber_le n 2 (by norm_num) (by omega)) ?_
  rw [SimpleGraph.le_chromaticNumber_iff_coloring]
  intro m Col
  set col : Finset (Fin n) → Option (Fin m) :=
    fun s => if h : s.card = 2 then some (Col ⟨s, h⟩) else none with hcoldef
  have hcol : ∀ a ∈ (Finset.univ : Finset (Fin n)).powersetCard 2,
      ∀ b ∈ (Finset.univ : Finset (Fin n)).powersetCard 2, Disjoint a b → col a ≠ col b := by
    intro a ha b hb hdisj
    rw [Finset.mem_powersetCard_univ] at ha hb
    have hne : (⟨a, ha⟩ : KneserVertex n 2) ≠ ⟨b, hb⟩ := by
      intro h
      have hab : a = b := congrArg Subtype.val h
      subst hab
      rw [disjoint_self, Finset.bot_eq_empty] at hdisj
      rw [hdisj] at ha
      simp at ha
    have hvalid := Col.valid (show (KneserGraph n 2).Adj ⟨a, ha⟩ ⟨b, hb⟩ from ⟨hne, hdisj⟩)
    simp only [hcoldef, ha, hb, dif_pos, ne_eq, Option.some.injEq]
    exact hvalid
  have hkey := card_image_ge_of_pair_coloring n (Finset.univ : Finset (Fin n)) (by simp) col hcol
  have hsub : ((Finset.univ : Finset (Fin n)).powersetCard 2).image col ⊆
      (Finset.univ : Finset (Fin m)).image some := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨e, he, rfl⟩ := hx
    rw [Finset.mem_powersetCard_univ] at he
    simp [hcoldef, he]
  have hcard :
      ((Finset.univ : Finset (Fin m)).image (some : Fin m → Option (Fin m))).card = m := by
    rw [Finset.card_image_of_injective _ (Option.some_injective _)]
    simp
  have hfin := le_trans hkey (le_trans (Finset.card_le_card hsub) (le_of_eq hcard))
  simp only [Finset.card_univ, Fintype.card_fin] at hfin
  have hfin2 : (n - 2 * 2 + 2 : ℕ) ≤ m := by omega
  exact_mod_cast hfin2

/-! ### The Lovász–Kneser theorem in the cases established here -/

/-- **Lovász's theorem on the chromatic number of Kneser graphs**, in the cases proved here:
the chromatic number of `KG_{n,k}` is `n - 2k + 2` whenever `1 ≤ k`, `2k ≤ n` and one of
`k = 1`, `k = 2`, `n = 2k` holds.

The general case (Lovász's theorem, whose usual proof goes through the Borsuk–Ulam theorem) is
not proved here; the upper bound `χ(KG_{n,k}) ≤ n - 2k + 2` is established in full generality
in `Frontier.kneser_chromaticNumber_le`. -/
