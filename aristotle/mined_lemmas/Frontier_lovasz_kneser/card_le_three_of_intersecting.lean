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

lemma card_le_three_of_intersecting (F : Finset (Finset ι))
    (hcard : ∀ e ∈ F, e.card = 2)
    (hint : ∀ e ∈ F, ∀ f ∈ F, ¬ Disjoint e f)
    (hnc : ∀ e ∈ F, ∀ v ∈ e, ∃ f ∈ F, v ∉ f) :
    F.card ≤ 3 := by
  rcases F.eq_empty_or_nonempty with rfl | ⟨e1, he1⟩
  · simp
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp (hcard e1 he1)
  -- `e2` avoids `a`, hence contains `b`
  obtain ⟨e2, he2, ha2⟩ := hnc _ he1 a (by simp)
  have hb2 : b ∈ e2 := by
    have h := hint _ he1 _ he2
    rw [Finset.not_disjoint_iff] at h
    obtain ⟨z, hz1, hz2⟩ := h
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz1
    rcases hz1 with rfl | rfl
    · exact absurd hz2 ha2
    · exact hz2
  obtain ⟨d, hdb, he2eq⟩ := exists_eq_pair_of_mem (hcard e2 he2) hb2
  have hda : d ≠ a := by
    rintro rfl
    exact ha2 (by rw [he2eq]; simp)
  -- `e3` avoids `b`, hence contains `a` and `d`
  obtain ⟨e3, he3, hb3⟩ := hnc _ he1 b (by simp)
  have ha3 : a ∈ e3 := by
    have h := hint _ he1 _ he3
    rw [Finset.not_disjoint_iff] at h
    obtain ⟨z, hz1, hz2⟩ := h
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz1
    rcases hz1 with rfl | rfl
    · exact hz2
    · exact absurd hz2 hb3
  obtain ⟨w, hwa, he3eq⟩ := exists_eq_pair_of_mem (hcard e3 he3) ha3
  have hbw : b ≠ w := by
    intro h
    exact hb3 (by rw [he3eq, ← h]; simp)
  have hwd : w = d := by
    have h := hint _ he2 _ he3
    rw [Finset.not_disjoint_iff] at h
    obtain ⟨z, hz1, hz2⟩ := h
    rw [he2eq] at hz1
    rw [he3eq] at hz2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz1 hz2
    rcases hz1 with h1 | h1 <;> rcases hz2 with h2 | h2
    · exact absurd (h1.symm.trans h2) (Ne.symm hab)
    · exact absurd (h1.symm.trans h2) hbw
    · exact absurd (h1.symm.trans h2) hda
    · exact (h1.symm.trans h2).symm
  subst hwd
  -- every member of `F` is contained in `{a, b, w}`
  have key : ∀ e ∈ F, e ⊆ ({a, b, w} : Finset ι) := by
    intro e he z hz
    by_contra hznot
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hznot
    obtain ⟨u, hu, heeq⟩ := exists_eq_pair_of_mem (hcard e he) hz
    have hmem : ∀ f ∈ F, ∀ x y : ι, f = {x, y} → z ≠ x → z ≠ y → (u = x ∨ u = y) := by
      intro f hf x y hfeq hzx hzy
      have h := hint _ he _ hf
      rw [Finset.not_disjoint_iff] at h
      obtain ⟨t, ht1, ht2⟩ := h
      rw [heeq] at ht1
      rw [hfeq] at ht2
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht1 ht2
      rcases ht1 with h1 | h1
      · rw [h1] at ht2
        rcases ht2 with h2 | h2
        · exact absurd h2 hzx
        · exact absurd h2 hzy
      · rw [h1] at ht2
        exact ht2
    have m1 := hmem _ he1 a b rfl hznot.1 hznot.2.1
    have m2 := hmem _ he2 b w he2eq hznot.2.1 hznot.2.2
    have m3 := hmem _ he3 a w he3eq hznot.1 hznot.2.2
    rcases m1 with h1 | h1
    · rcases m2 with h | h
      · exact hab (h1.symm.trans h)
      · exact hwa (h.symm.trans h1)
    · rcases m3 with h | h
      · exact hab (h.symm.trans h1)
      · exact hbw (h1.symm.trans h)
  have hsub : F ⊆ ({a, b, w} : Finset ι).powersetCard 2 := by
    intro e he
    rw [Finset.mem_powersetCard]
    exact ⟨key e he, hcard e he⟩
  have hc3 : ({a, b, w} : Finset ι).card = 3 := by
    have h1 : a ∉ ({b, w} : Finset ι) := by simp [hab, Ne.symm hwa]
    have h2 : b ∉ ({w} : Finset ι) := by simp [hbw]
    rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2, Finset.card_singleton]
  calc F.card ≤ (({a, b, w} : Finset ι).powersetCard 2).card := Finset.card_le_card hsub
    _ = 3 := by rw [Finset.card_powersetCard, hc3]; decide

